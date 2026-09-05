# Float-exactify backlog — the genuine float-decision set (2026-08-27)

The no-float sweep classified ~8,100 flagged lines. Safe buckets (DISPLAY 911, STAT 633,
SKLEARN 19) are NOT mass-annotated — an unverifiable justification is itself a rubber-stamp.
REVIEW-OTHER (6,289) are intermediate float computations, provisional under the CLAUDE.md
provenance clause. This file is the ONLY must-act set: **68 genuine float-exactness-decisions**.

**Finding: all 68 are MODEL-SCALE** (|·|~O(√p), p≤~200) where float error ~1e-13 sits far below
the tolerances, OR high-precision Sage (CF-212), OR statistical. **None operate on 256-bit keys.**
So none manufacture a false verdict today; this is a rigor/compliance backlog, priority = the two
nearest the float floor (d2_twist 1e-12, subrayleigh 1e-11). Fix = exact CyclotomicField '==' /
integer check, or a justified '# noqa: float' where the quantity is genuinely a ranked statistic.

```
GENUINE float-exactness-decision lines (deduped, benign/Sage/stat excluded): 68

  _method_review_v1.py:77: if abs(U) < 1e-12: continue
  _smoke_logic_v1.sage.py:39: if abs(eigs[j] / eigs[i] - Z3) < TOL_PAIR:
  analysis_capability_v5.py:84: if abs(A[piv][c]) < 1e-18:
  analysis_scaling_v4.py:105: if abs(det) < 1e-15:
  audit_d2_bridge_reduction_v1.py:219: if abs(d) < abs(s) * 1e-15:
  audit_d2_bridge_reduction_v1.py:239: if abs(de - 1.0) < 1e-15:
  blinded_joint_readout_v1.py:484: c2_pass = (abs(results["M"]["TDECOY"]["z"]) < 2.0 and
  blinded_joint_readout_v1.py:485: abs(results["S"]["TDECOY"]["z"]) < 2.0)
  conservation_spectrum_v2.py:144: elif aA > 0.6 and abs(arg) < 30:
  coord_interference_v1.py:100: frac_near_int = float(np.mean(np.abs(vals - nearest) < 0.02 * np.maximum(nearest, 1)))
  coord_interference_v1.py:102: frac_at_1 = float(np.mean(np.abs(vals - 1.0) < 0.02))
  curve_native_beam_scan_v2.py:58: ok = (np.std(cl) < 1e-6) and (np.std(cn) < 1e-6)
  d2_twist_rigidity_certificate_v1.py:268: base_ok = all(abs(abs(r) - sqp) / sqp < 1e-12 for r in base) and \
  d2_twist_rigidity_certificate_v1.py:269: all(min(abs((r / sqp) ** m - 1) for m in (3, 6)) < 1e-12 for r in base)
  glv_amicable_geometry_verify_v1.py:62: print(f"   colleague claimed 0.9999939561 -> {'MATCH' if abs(float(F(inter,aPp))-0.9999939561)<1e-9 
  glv_pinned_satotate_v1.py:72: f"{'ok' if abs(th - thf) < 1e-6 or abs(th - thf - 60) < 1e-6 else 'DIFF'}")
  glv_pinned_satotate_v1.py:82: f"{'== t-form' if abs(th-thf)<1e-3 else 'DIFF'}")
  gram_spectrum_exact_v1.py:102: good = (r["circ"] < 1e-6 and r["maxdiff"] < 1e-6 and r["distinct"] == 2
  harmonic_deficit_locus_v2.py:150: print(f"  C1 equivariance <1e-6 all primes: {all(r['C1_equiv']<1e-6 for r in disc+repl)}", flush=Tru
  harmonic_support_pattern_v1.py:163: c1 = rel < 1e-6
  harmonic_support_pattern_v1.py:187: c2 = c2err < 1e-6
  int2_rank10_mu3_v1.py:76: f"offdiag max={offmax:.4f}  ({'ORTHOGONAL (rank-10)' if ev[0]/ev[-1] < 1.3 and offmax < 1e-6*sub.sha
  int2b_rank10_prime_split_v1.py:71: f"both orthogonal={np.max(np.abs((F[:,curve6].conj().T@F[:,flap4])))<1e-6}")
  int2b_rank10_prime_split_v1.py:73: f"both orthogonal={np.max(np.abs((F[:,rnd6].conj().T@F[:,rnd4])))<1e-6}")
  intensity_parseval_orbit_null_v1.py:101: rs_ok = np.allclose(J[1:, 1:].sum(axis=1), I[1:, 1:].sum(axis=1), atol=tol)
  intensity_parseval_orbit_null_v1.py:103: par_ok = np.allclose(J[1:, a], J[1:, (n - a) % n], atol=tol)
  lmono_gkr_coset_discriminator_v1.py:111: print(f"  -> data selects {'DIAGONAL' if abs(m4-2.0) < abs(m4-7.0) else 'INDEPENDENT'};"
  lmono_gkr_moment_fingerprint_v1.py:66: assert abs(val - r) < 1e-9, f"non-integer cyclotomic sum at ({a},{b}): {val}"
  lmono_gkr_moment_fingerprint_v1.py:143: assert abs(val - r) < 1e-6, (a, b, val)
  lmono_gkr_rank4_eigenderiv_v1.py:139: ok = (worst["e2"] < 1e-10 and worst["e3"] < 1e-10 and worst["e4"] < 1e-10 and
  lmono_gkr_rank4_eigenderiv_v1.py:140: worst["trace_imag_real"] < 1e-10 and worst["claim2_V1"] < 1e-10 and
  lmono_gkr_rank4_eigenderiv_v1.py:141: worst["halftrace_imag"] < 1e-10 and worst["claim3_t"] < 1e-10)
  lmono_routeB_geom_iso_certificate_v1.py:88: and f3_purity < 1e-9 and f3_rou > 1e-6)
  m40_n15_exact_accounting_v1.py:218: f"({'FLAT (<= noise 1e-3)' if MI < 1e-3 else 'NONZERO - group-law coupling!'})")
  mu3_glv_frequency_support_v1.py:220: print(f"[selftest] (i) brute-U vs FFT-path |U| max err = {err:.2e}  ok={err < 1e-8}")
  mu3_glv_frequency_support_v1.py:228: print(f"[selftest] (ii) forced-diagonal intra-orbit Var(|U|) max = {mx:.2e}  ok={mx < 1e-6}")
  mu3_glv_frequency_support_v1.py:239: ok = err < 1e-8 and mx < 1e-6 and abs(E-emp.mean()) < 0.05
  mu3_phase_within_triple_v1.py:123: print(f"[selftest] (ii) gauge flip (u->conj u) P_obs delta = {abs(Pf-P_obs(r,tri)):.2e}  ok={abs(Pf-
  mu3_phase_within_triple_v1.py:131: ok = okm and abs(Pf-P_obs(r,tri)) < 1e-6 and zp > 5 and abs(zn) < 4 and abs(zg-z0) < 1e-6
  mu6_cohomology_split_v1.py:81: if not used[j] and abs(eg[i].conjugate()-eg[j]) < 1e-5:
  mu6_cohomology_split_v3.py:59: if abs(z**m - 1) < 1e-6: return m
  n1_exact_saturation_v1.py:51: frac_int = float((dev < 1e-6).mean())
  n1_flap_bridge_v1.py:103: assert np.max(np.abs(V1 - (Vf + Vc))) < 1e-6, "split is not additive"
  n1_flap_bridge_v2.py:75: split_ok = np.max(np.abs(V1 - (Vf + Vc))) < 1e-6           # I2
  n1_phase_cap_v2_controls.py:65: ok = rel <= 1e-10 and S > 2
  n1_phase_cap_v2_controls.py:80: ok_f &= (rel <= 1e-10 and spread <= 1e-10)
  n1_sheaf_cm_type_probe_v1.sage.py:337: if abs(eigs[j] / eigs[i] - Z3) < TOL_PAIR:
  n1_sheaf_newton_diag_v1.sage.py:79: if abs(eigs[j] / eigs[i] - Z3) < TOL_PAIR or abs(eigs[j] / eigs[i] - Z3 ** _sage_const_2 ) < TOL_PAI
  powersum_ladder_routeA_v1.sage.py:103: print(f"CONTROL C2 (plant recovery): max|recovered-planted|={float(err):.2e}  fires={err<1e-6}\n")
  q4_principal_survival.py:55: print(f"  m1={m1},m2={m2}: c_(m1m2)(1)={lhs.real:+.1f}  vs  c_(m1)c_(m2)={rhs.real:+.1f}  match={abs
  subrayleigh_deficit_locus_v1.py:168: eqok = pair_ok and eqerr < 1e-11
  subrayleigh_deficit_locus_v1.py:266: % (A4_fft, A4_exact, cx, "OK" if cx < 1e-9 else "FAIL"))
  subrayleigh_deficit_locus_v1.py:295: % (p5, "FIRED" if p5 < 1e-9 else "DID NOT FIRE"))
  subrayleigh_deficit_locus_v1.py:300: eq=eqok, n10=n10, c10=c10, p1=p1, p2=(z4p > 5), p5=(p5 < 1e-9),
  subrayleigh_deficit_locus_v1.py:387: % (all(r["eq"] for r in out), all(r["cx"] < 1e-9 for r in out),
  subrayleigh_deficit_scaling_v1.py:166: f"relerr={r['parseval_relerr']:.2e}  {'PASS' if r['parseval_relerr']<1e-6 else 'FAIL'}")
  supersingular_mu4_mechanism_v1.py:67: if not (abs(z) - 1).abs() < 1e-9:
  transfer_operator_rmt_battery_v1.py:66: z = ev[np.abs(ev) < 0.999999]                      # drop the Perron eigenvalue 1
  transfer_operator_rmt_battery_v1.py:100: cnt = np.array([np.sum(np.abs(z - c) < R0) for c in ctrs], dtype=float)
  transfer_operator_rmt_battery_v1.py:159: np.sum(np.abs(ev) < 0.999999)))
  weight1_phase_ramp_v1.py:112: if mag < 1e-12: degen += 1
  weyl_xreadout_item4_v1.py:158: ok_c = all(abs(c[o[1][0]] - zeta*c[o[0][0]]) < 1e-9
  weyl_xreadout_item4_v1.py:159: and abs(c[o[2][0]] - zeta*zeta*c[o[0][0]]) < 1e-9
  weyl_xreadout_item4_v1.py:160: and all(abs(c[lv[1]] - c[lv[0]]) < 1e-9 for lv in o) for o in cls)
  weyl_xreadout_item4_v1.py:165: real_readout = bool(np.max(np.abs(np.imag(c))) < 1e-12)
  weyl_xreadout_item4_v1.py:173: ok_a = all(np.allclose(Hm[o], Hm[o[0]], atol=1e-6*max(1, Hm.max())) for o in acls)
  xdomain_derivation_checks_v1.py:157: ok = all(w < 1e-8 for *_, w, _ in r)
  y_channel_chi2_vs_axis_v2.py:67: chan_ok = (abs(reV) < 1e-6) if p3 else True
```
