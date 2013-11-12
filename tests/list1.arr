#lang pyret

#! 1st argument was expected to be of type String, but was the incompatible type Number

fun f(n :: String) -> String:
  n
end

f([].length())