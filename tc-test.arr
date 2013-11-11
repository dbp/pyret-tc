#lang pyret

################################################################################
#                                                                              #
# This file contains the test runner for the accompanying type checker.        #
# All work (c) 2013 Daniel Patterson <dbp@dbpmail.net>.                        #
#                                                                              #
# Permission to use, copy, modify, and/or distribute this software for         #
# any purpose with or without fee is hereby granted, provided that the         #
# above copyright notice and this permission notice appear in all              #
# copies.                                                                      #
#                                                                              #
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL                #
# WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED                #
# WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE             #
# AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL         #
# DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA           #
# OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER            #
# TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR             #
# PERFORMANCE OF THIS SOFTWARE.                                                #
#                                                                              #
################################################################################


import "tc.arr" as tc
import Racket as Racket
import file as F
import directory as D

################################################################################
# Testing harness helpers.                                                     #
################################################################################

data Pair:
  | pair(a,b)
sharing:
  _equals(self, other):
    is-pair(other) and (self.a == other.a) and (self.b == other.b)
  end
end

fun build-path(parts):
  parts.join-str("/")
end
fun str-ends-with(s1,s2):
  s1.substring(s1.length() - s2.length(), s1.length()) == s2
end
fun str-starts-with(s1,s2):
  s1.substring(0, s2.length()) == s2
end
fun strip-ext(s):
  s.substring(0, s.length() - 4)
end

fun is-code-file(path):
  path^str-ends-with(".arr") and (not path^str-starts-with("."))
end


################################################################################
# Testing harness commandline driver.                                          #
################################################################################

var files = []
baseR = Racket("racket/base")
cmdlineargs = baseR("vector->list", baseR("current-command-line-arguments"))

fun format-errors(ers):
  cases(List) ers:
    | empty => "No type errors detected."
    | link(_,_) => ers.map(torepr).join-str("\n")
  end
end
if cmdlineargs.length() == 1:
  files := D.dir("tests").list().map(fun(path): build-path(["tests", path]) end)
  nothing
else:
  files := [cmdlineargs.last()]
  nothing
end

check:
  files.each(fun(path):
      when is-code-file(path):
        # NOTE(dbp 2013-09-29): We run the .arr file. It expects to
        # have a corresponding .err file.  if .err is non-empty, we
        # expect to see an error that matches the content of that
        # file. If it is empty, we expect it to produce nothing as the
        # output of type checking.
        stripped = strip-ext(path)
        print("Running " + stripped)
        errpath = stripped + ".err"
        code = F.input-file(path).read-file()
        err = F.input-file(errpath).read-file()
        if err.length() <> 0:
          err-msg = format-errors(tc.file(path, code))
          pair(path,pair(err-msg, err-msg.contains(err)))
          is pair(path, pair(err-msg, true))
        else:
          err-msg = format-errors(tc.file(path, code))
          pair(path, pair(err-msg,
              err-msg.contains("No type errors detected.")))
          is pair(path,pair(err-msg, true))
        end
      end
    end)
end