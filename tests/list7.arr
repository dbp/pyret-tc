#lang pyret

fun stn(x :: String) -> Number:
  x.tonumber()
end

x :: List<String> = map(stn, ["foo"])