#lang pyret

#! During inference, a unification error occurred. Could not match types: Number and String

# Old error:
# #! identifier x was defined to have type List<String>, but assigned a value of an incompatible type: List<Number>

fun stn(x :: String) -> Number:
  x.tonumber()
end

x :: List<String> = map(stn, ["foo"])