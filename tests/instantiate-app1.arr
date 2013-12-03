#lang pyret

#==

fun<T> foo(a :: T) -> Option<T>:
  some<T>(a)
end

foo<Number>(20)