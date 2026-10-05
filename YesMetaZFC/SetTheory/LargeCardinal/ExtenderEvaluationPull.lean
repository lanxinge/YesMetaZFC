import YesMetaZFC.SetTheory.LargeCardinal.ExtenderEvaluation

/-! # 原求值与有限坐标过渡交换 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ee_pull_l (hZF : M.Models ZF) {ω δ X A Y B j κ k K R L m n q a b f g y z : M.Domain}
    (source : Ep_source_d hZF ω κ K X R)
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k)
    (hL : M.MemberSubset L k) (hm : M.mem m ω) (hn : M.mem n ω) (hq : Fn0_d m n q)
    (ha : M.mem a Y) (hb : M.mem b Y) (hnb : Fn0_d n L b) (hqa : Cp0_d m n L q b a)
    (hfX : M.mem f X) (pull : Ep_pull_d κ X m n q f g)
    (hy : Ee_value_d j a f y) (hz : Ee_value_d j b g z) : y = z := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  obtain ⟨D, hD, hf⟩ := pull.1
  obtain ⟨E, hE, hg⟩ := pull.2.1
  have hωκ := ed_critical_omega_l I hZF source.omega h source.transitive hY hc
  obtain ⟨E', D', t, t', hjE, hjD, ht, ts, hjt, htb⟩ := ed_reindex_l I hZF source.omega hV hδ h hY hc
    (hc.ordinal.transitive ω hωκ m hm) (hc.ordinal.transitive ω hωκ n hn) hq hE hD hL hb ha hnb hqa
  obtain ⟨_, C, hCX, hFC⟩ := source.function_l hZF hfX hf
  have comp : Cp0_d E D X t f g := by
    refine ⟨hg, fun s hs => ?_⟩
    obtain ⟨r, hr, hsr⟩ := ht.2.1 s hs
    obtain ⟨x, hx, hrx⟩ := hf.2.1 r hr
    exact ⟨r, hr, x, hx, hsr, hrx, (pull.2.2 s r ((hE s).mp hs) ((ts s r).mp hsr).2 x).mpr hrx⟩
  obtain ⟨C', _, hjC⟩ := hj.2.2 C hCX
  obtain ⟨f', hjf, haf⟩ := hy
  obtain ⟨g', hjg, hbg⟩ := hz
  let φ : Formula 1 6 := cp0_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  have tr := spred_delta_l I hZF source.omega h source.transitive hY φ (by simp -implicitDefEqProofs [φ]) (cp0_delta_l ..)
    ⟨Fin.cases g (Fin.cases f (Fin.cases t (Fin.cases C (Fin.cases D (fun _ => E))))), fun _ => E⟩
    ⟨Fin.cases g' (Fin.cases f' (Fin.cases t' (Fin.cases C' (Fin.cases D' (fun _ => E'))))), fun _ => E'⟩
    (Fin.cases hjg (Fin.cases hjf (Fin.cases hjt (Fin.cases hjC (Fin.cases hjD (fun _ => hjE))))))
  simp only [φ, cp0_sat_l hZF.1] at tr
  have comp' := tr.mp (comp.retarget_l hFC)
  have ht' := (spred_function_l I hZF source.omega h source.transitive hY hjE hjD hjt).mp ht
  have hf' := (spred_function_l I hZF source.omega h source.transitive hY hjD hjC hjf).mp hFC
  exact (fn0_function_l (ZF.modelsKP hZF) hf').1.2 a y z haf ((comp'.value_l ht' hf' htb).mp hbg)

end YesMetaZFC.SetTheory.LargeCardinal
