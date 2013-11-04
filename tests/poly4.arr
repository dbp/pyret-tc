#lang pyret

fun<T> id(x :: T) -> T:
  t
end

fun f(x :: String) -> String:
  x
end

f(id(19))