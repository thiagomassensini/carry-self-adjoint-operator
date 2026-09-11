# Completed native TFVD enriched low-order moment test

This audit starts at commit `d2c602065fc16b770224e4a8f4c9f3ce20d4509b` on branch
`agent/enriched-tfvd-moment-low-order-test`.  It tests the existing carrier
`canonicalCompletedNativeTfvdEnrichedTaylorRawJet` against the canonical
polarized moment equation without introducing a camera, a cutoff limit, a
phase convention, or a fitted normalization.

## Carrier and the first Gram entry

The carrier is the orthogonal pair

```text
(T_p, L_p)
```

with `T_p = canonicalCompletedNativeTfvdTaylorCoefficientState p` and
`L_p = canonicalCompletedNativeTfvdLogTaylorCoefficientState p`.  Its Gram is
already split by the exact theorem

```lean
inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet
```

into the ordinary and logarithmic channel Grams.  At order zero the existing
state identifications give the following exact real channel formulas:

```lean
enrichedTfvdTaylorZeroZeroOrdinaryGram_re_eq_reflectedGreen
enrichedTfvdTaylorZeroZeroLogGram_re_eq_logJetNormSq
```

Consequently the full zeroth Gram has real part

$$
\operatorname{Re}\langle v_0,v_0\rangle
=
\operatorname{infiniteReflectedGreenEnergy}(1/2)
+\|L_0\|^2.
$$

The combined identity is exported as

```lean
enrichedTfvdTaylorZeroZeroGram_re_eq_reflectedGreen_add_logJet
enrichedTfvdTaylorZeroZeroGram_eq_ofReal
```

The second theorem records the complete complex self-Gram: it is the cast to
`ℂ` of the displayed real channel sum (the imaginary part vanishes by the
standard self-inner-product identity).  The defect relative to the canonical native moment is the explicit real
quantity

```lean
def enrichedTfvdTaylorZeroZeroDefect : ℝ :=
  (inner ℂ (rawJet 0) (rawJet 0)).re -
    canonicalCompletedNativeLogDerivativeMoment 0
```

with its exact channel expansion in
`enrichedTfvdTaylorZeroZeroDefect_eq_channelGrams_sub_native` and its
reflected-energy expansion in
`enrichedTfvdTaylorZeroZeroDefect_eq_reflectedGreen_add_logJet_sub_native`.

## Kernel-checked result

The already-proved central bounds are

```lean
canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
infiniteReflectedGreenEnergy_half_gt_sixteenth
```

Together with `sq_nonneg ‖L_0‖`, they prove

```lean
enrichedTfvdTaylorZeroZeroDefect_pos
```

and hence

```lean
enrichedTfvdTaylor_zero_zero_gram_re_gt_native
```

That is,

$$
 h_0 < \operatorname{Re}\langle v_0,v_0\rangle.
$$

Therefore the desired complex equality at `(p,q)=(0,0)` is false:

```lean
enrichedTfvdTaylor_zero_zero_ne_moment
```

and the full all-order vector equation is refuted already by this entry:

```lean
not_hasPolarizedCoefficientVectorEquation_enrichedTfvdTaylor
```

The contradiction is obtained by applying `Complex.re` to the purported
complex `(0,0)` equality.  No numerical computation is involved.

## Scope decision

The `(0,0)` obstruction is fatal for this carrier, so the requested `(0,1)`
and `(1,1)` tests are not promoted to unconditional claims in this module.
The existing conditional theorem `enrichedTfvdTaylorEquation_zero_one` remains
an implication from the unavailable all-order coefficient equation; it does
not repair the zeroth mismatch.  No phase or realification change is applied.

This is **Outcome C**: the ordinary-plus-logarithmic enriched TFVD Taylor
carrier is formally refuted as a realization of the canonical native moment
Gram by its positive central defect.  The result does not refute a different
carrier or a transported metric.

## Validation

The module and its audit print the axioms of every load-bearing declaration.
The allowed footprint is the standard one (`propext`, `Classical.choice`, and
`Quot.sound`).  The repository checks are:

```text
lake build
bash scripts/audit.sh
git diff --check
python3 -m json.tool audit/theorem-registry.json
```
