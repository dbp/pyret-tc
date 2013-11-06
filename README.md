# How to use

You must have Pyret installed. See
[github.com/brownplt/pyret-lang](https://github.com/brownplt/pyret-lang).

Next:

    git clone https://github.com/dbp/pyret-tc

And then run:

    raco pyret --no-checks tc.arr report /path/to/file.arr

Which will print out a report from type checking, listing any errors
detected, and any top level functions that it inferred types for based
on tests.

Feedback welcome; though it is definitely still a work in progress
(so, "it doesn't catch all type errors" isn't useful feedback. A
specific error it missed, on the other hand, is.)


# Running tests

If you want to run the type checkers test suite (all the programs in
the `tests` directory, as well as unit tests in `tc.arr`), run:

    raco pyret tc.arr tests

If you want to only run the unit tests:

    raco pyret tc.arr

And to run a specific file test:

    raco pyret tc.arr tests/basic1.arr