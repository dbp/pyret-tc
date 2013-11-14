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
# Note about test file format:                                                 #
#                                                                              #
# The tests are .arr files that have special comments in them indicating       #
# warnings or errors that should occur. Any line starting with:                #
# '#! ' is interpreted to be a string that should match against an error, for  #
# example, '#! identifier x was defined to have type List<String>'.            #
#                                                                              #
# Warnings should start with '#~ ', and have the same pattern. The placement   #
# of these comments does not matter, but at least currently, the convention is #
# to place them all at the top of the file.                                    #
#                                                                              #
# Finally, the special marker #= means that there should be no errors, and #== #
# means no warnings as well.                                                   #
################################################################################


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

fun splitn(str :: String, needle :: String) -> List<String>:
  doc: "Keep splitting (like I wish the string split method would)"
  x = str.split(needle, false)
  if x.length() == 1:
    x
  else:
    link(x.first, splitn(x.rest.first, needle))
  end
end


################################################################################
# Testing harness commandline driver.                                          #
################################################################################

var files = []
baseR = Racket("racket/base")
cmdlineargs = baseR("vector->list", baseR("current-command-line-arguments"))

if cmdlineargs.length() == 1:
  files := D.dir("tests").list().map(fun(path): build-path(["tests", path]) end)
  nothing
else:
  files := [cmdlineargs.last()]
  nothing
end


fun format-lines(ers):
  cases(List) ers:
    | empty => ""
    | link(_,_) => ers.map(_.b).map(tostring).join-str("\n")
  end
end

data EWConfig:
  | errsWarns(errors :: List<String>, warns :: List<String>)
  | noErrs(warns :: List<String>)
  | noErrsWarns
end

fun extract-errs-warns(fname :: String, c :: String) -> EWConfig:
  var ers = []
  var wrns = []
  var noers = false
  var noerswrns = false
  fun h(s :: List<String>) -> Nothing:
    cases(List) s:
      | empty => nothing
      | link(f, r) =>
        if str-starts-with(f, "#=="):
          noerswrns := true
        else if str-starts-with(f, "#="):
          noers := true
        else if str-starts-with(f, "#! "):
          ers := ers + [f.substring(3, 1000000)]
        else if str-starts-with(f, "#~ "):
          wrns := wrns + [f.substring(3, 1000000)]
        else:
          nothing
        end
        h(r)
    end
  end
  h(splitn(c, "\n").map(tostring))
  if noerswrns:
    if (ers <> []) or (wrns <> []):
      raise("tc-test: error in test file " + fname + ", has #== and error/warning markers.")
    else:
      noErrsWarns
    end
  else if noers:
    if ers <> []:
      raise("tc-test: error in test file " + fname + ", has #== and error markers.")
    else:
      noErrs(wrns)
    end
  else:
    if (ers == []) and (wrns == []):
      raise("tc-test: test file " + fname + " did not declare any errors, warnings, or that it shouldn't have them.")
    else:
      errsWarns(ers, wrns)
    end
  end
where:
  # NOTE(dbp 2013-11-11): I'm commenting these out because they distort the test count. Errp..
  # When editing the above function, uncomment them!
  #
  # extract-errs-warns("", "#== \nfoo\nbar\n#blah") is noErrsWarns
  # extract-errs-warns("", "#= \nfoo\nbar\n#~ some warning\n") is noErrs(["some warning"])
  # extract-errs-warns("", "#! something\nfoo\nbar\n#~ some warning\n")
  # is errsWarns(["something"],["some warning"])
end


# NOTE(dbp 2013-11-11): This silliness is to get the things that are printed out on
# failing tests to be friendly.
data ErrWarnPair:
  | errPair(msg, ers)
  | warnPair(msg, ers)
end

fun ew-contains(ew):
  ew.ers.contains(ew.msg)
end

data NoErrsWarns:
  | noErrorsIn(ers)
  | noWarnsIn(ers)
end

fun is-blank(noe):
  noe.ers == ""
end

check:
  files.each(fun(path):
      when is-code-file(path):
        print("Running " + path)
        code = F.input-file(path).read-file()

        result = tc.file(path, code)
        fmtd-errs = format-lines(result.errors)
        fmtd-warns = format-lines(result.warnings)

        cases(EWConfig) extract-errs-warns(path, code):
          | errsWarns(errors, warns) =>
            for each(err from errors):
              errPair(err, fmtd-errs) satisfies ew-contains
            end
            for each(warn from warns):
              warnPair(warn, fmtd-warns) satisfies ew-contains
            end
          | noErrs(warns) =>
            noErrorsIn(fmtd-errs) satisfies is-blank
            for each(warn from warns):
              warnPair(warn, fmtd-warns) satisfies ew-contains
            end
          | noErrsWarns =>
            noErrorsIn(fmtd-errs) satisfies is-blank
            noWarnsIn(fmtd-warns) satisfies is-blank
        end

      end
    end)
end