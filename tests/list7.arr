#lang pyret

#! identifier x was defined to have type List<String>, but assigned a value of an incompatible type: List<Number>

fun stn(x :: String) -> Number:
  x.tonumber()
end

x :: List<String> = map(stn, ["foo"])