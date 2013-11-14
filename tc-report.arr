#lang pyret

################################################################################
#                                                                              #
# This file contains the commandline runner for the accompanying type checker. #
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

fun pretty-error(ep :: {a :: {line :: Number, column :: Number}, b :: String}) -> String:
  "Line " + tostring(ep.a.line) + ", Column " + tostring(ep.a.column) + " - " + ep.b
end

fun pretty-iif(iif) -> String:
  "fun " + iif.a + " :: " + tc.format-type(iif.b)
end

fun tc-report(p, s):
  print("Report for " + p + ":")
  result = tc.main(p,s)
  if result.errors.length() <> 0:
    print("\n\nErrors detected:\n")
    print(result.errors.map(pretty-error).join-str("\n"))
  else:
    print("\n\nNo type errors detected.")
  end
  if result.warnings.length() <> 0:
    print("\n\nWarnings detected:\n")
    print(result.warnings.map(pretty-error).join-str("\n"))
  else:
    print("\n\nNo type warnings detected.")
  end
  when result.iifs.length() <> 0:
    print("\n\nTop level inferred functions:\n")
    print(result.iifs.map(pretty-iif).join-str("\n"))
  end
  print("\n")
end

baseR = Racket("racket/base")
cmdlineargs = baseR("vector->list", baseR("current-command-line-arguments"))

fun usage():
  print("Usage:\n    raco pyret tc-report.arr /path/to/file.arr\n")
  nothing
end

if cmdlineargs.length() == 1:
  usage()
else:
  path = cmdlineargs.last()
  tc-report(path, F.input-file(path).read-file())
  nothing
end
