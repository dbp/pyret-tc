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
  tc.report(path, F.input-file(path).read-file())
  nothing
end
