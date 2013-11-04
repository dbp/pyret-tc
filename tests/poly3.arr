#lang pyret

fun<T> id(x :: T) -> T:
  x
end

fun f(x :: String) -> String:
  x
end

f(id("Foo"))