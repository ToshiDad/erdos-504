# Erdos Problem 504 (work in progress)
Formalisation of Szekeres (1941) and Erdos-Szekeres (1960) on the minimax angle problem, in Lean 4.33.0 + Mathlib.

Sorry-free, axioms: propext, Classical.choice, Quot.sound. Main results:
- exists_angle_gt: any set of more than 2^n points in the plane determines an angle greater than (1-1/n)*pi (Szekeres 1941, lower bound).
- exists_config_angle_lt: for every eps > 0 there is a set of exactly 2^n points with all angles less than (1-1/n)*pi + eps (Szekeres 1941, upper-bound construction).

Together these determine the minimax angle at m = 2^n up to the endpoint question settled by Erdos-Szekeres 1960 (in progress).
