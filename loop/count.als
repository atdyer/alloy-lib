

-- count even numbers in a sequence

module count

open util/relation

sig S {
  f: seq Int
}

pred c1 [s: seq Int, count: Int] {
  count = #{ i: dom[s] | rem[s[i], 2] = 0 }
}

pred c2 [s: seq Int, count: Int] {
  some c: seq Int {
    c[0] = 0
    #c = add[#s, 1]
    all i: dom[s] |
      let t = i, t' = add[i, 1] |
        rem[s[i], 2] = 0 =>
          c[t'] = add[c[t], 1]   -- even, so increment counter
            else c[t'] = c[t]    -- not even, so stutter
    count = c.last
  }
}

-- show a sequence of 2 integers with exactly 2 of them even

pred show {
--  some s: S | #s.f = 3 and c1[S.f, 2]
  some s: S | #s.f = 3 and c2[S.f, 2]
}
  
run show for 6 but 1 S, 4 Int

--  can't perform a comparison because c2 cannot be skolemized

assert sameCount {
  all s: seq Int, count: Int |
    c1[s, count] <=> c2[s, count]
}

check sameCount for 6 but 1 S, 4 Int
