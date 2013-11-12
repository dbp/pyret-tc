#lang pyret

#! Function with type ((T -> Bool) -> List<T>) not compatible with arguments (Dyn* -> Number)

fun f(x) -> Number:
  1
end

[].filter(f)