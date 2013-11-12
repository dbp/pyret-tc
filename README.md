# How to use

You must have Pyret installed. See
[github.com/brownplt/pyret-lang](https://github.com/brownplt/pyret-lang).

Next:

    git clone https://github.com/dbp/pyret-tc

And then build it:

    raco make tc.arr

(This will take a while - on my desktop, it takes ~40 seconds. On a
recent laptop, it should take maybe double that.)

Now run:

    raco pyret tc-report.arr /path/to/file.arr

Which will print out a report from type checking, listing any errors
detected, and any top level functions that it inferred types for based
on tests.

Feedback welcome; though it is definitely still a work in progress
(so, "it doesn't catch all type errors" isn't useful feedback. A
specific error it missed, on the other hand, is.)


# Running tests

If you want to run the type checkers test suite (all the programs in
the `tests` directory), you can run:

    raco pyret tc-test.arr

Or to run a specific test:

    raco pyret tc-test.arr test/functions1.arr

The tests are normal Pyret programs that have information in special comments
that specify what errors and warnings, if any, the program should result in.


If you'd like to run the unit tests inside the type checker, you have
to first clear out the compiled code from `raco make` above:

    rm -r compiled/

Now run:

    raco pyret tc.arr
