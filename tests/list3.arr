#lang pyret

#! identifier x was defined to have type String, but assigned a value of an incompatible type: List<Dyn*>

x :: String = [].reverse()