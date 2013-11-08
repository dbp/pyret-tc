#lang pyret

fun foo(x :: String) -> String:
  x
end

cases(List<String>) ["hola"]:
  | empty => "hello"
  | link(f, r) => foo(f)
end