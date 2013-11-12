#lang pyret

#! 1st argument was expected to be of type String, but was the incompatible type Number

fun<T> id(x :: T) -> T:
  x
end

fun f(x :: String) -> String:
  x
end

f(id(19))