import Leanplayground.Natural4.Test
import Leanplayground.Natural4
import Leanplayground.Primes.PrimeSieve

import Verso.Genre.Blog

open Verso Genre Blog Site Syntax in
def main (options : List String) : IO UInt32 := do
  let n ← blogMain Theme.default natural4site options
  if n > 0 then IO.println s!"Error occured with code: {n}"
  return n
where
  natural4site := site Leanplayground.Natural4

-- #eval main []
