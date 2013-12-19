#lang pyret

#! During inference, a unification error occurred. Could not match types: Number and String
# Old error:
# #! 1st argument was expected to be of type Option<String>, but was the incompatible type Option<Number>

fun foo(x :: Option<String>):
  nothing
end

foo(some(19))