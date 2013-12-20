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


If you'd like to run the unit tests built into the type checker, you can run:

    raco pyret tc-unit.arr

**NOTE**: This is a hack - tc-unit.arr is just a symlink to tc.arr,
  because once you `raco make tc.arr`, if you try to run it, it will
  run the compiled version, which doesn't have the unit tests. So
  instead we run the same file with a different name (by way of a
  symlink) and it all works.  If you are on a platform that doesn't
  have symlinks, this probably won't work, and you can just removed
  the `compiled` directory and then run `raco pyret tc.arr`.

# TODOS / Questions

- Unification errors don't have location information. This is an easy
  fix - it just means adding location information to all the ConTerms,
  so when we have two that don't match, we can specify where they
  occurred.

- Subtyping during unification? This has come up with records, where
  you have a dotted expression - this means the operand on the left
  side must be a subtype of the record with the field on the right
  side (and there is type information too). Right now, when two
  records are compared, the right is presumed to be a supertype of the
  left, but I'm not sure if this is a good invariant. Subtyping also
  comes up with the top type, Any, and right now unification is not
  handling that (the cause of one of the couple test cases that is
  failing.)

- Use inference for more? Right now, if there are no uninstantiated
  type parameters, the unification based inference does not even
  happen. Further, we only use the results of the instantiated type
  parameters (not, for example, let bindings). The latter is an
  obvious improvement (as we have discovered type information, we
  shouldn't throw it out). The former is a more interesting question -
  unification gives worse error messages, generally, which is the
  reason for the current decision, but if works well enough, it also
  removes the need for type checking at all, which would shorten (if
  not simplify) things. Additionally, I don't think it would be that
  hard to extend the unification to the whole program (there are some
  things that get harder, but I'm not sure by how much).