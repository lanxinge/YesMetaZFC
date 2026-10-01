import YesMetaZFC.Model.Forcing.TwoStep.Names.Construction

/-! # 两步名称转换后的第二阶段名称性

对原名称闭支撑上的转换值作实际替换，并把值域解释成第一扩张内的支撑集。
条目的标签属于第二阶段条件集，由首阶段成员力迫及真值定理验证。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
include O hZF hU

/-- 第一阶段解释精确展开转换名称的成员，包括被接受的第一坐标及第二坐标解释。 -/
theorem curry_val_mem_l (h : Two_step_d M B R z b A T W C S)
    {x t} (ht : Curry_d M B C x t) {v r : (E).Domain} (hv : Qval_d M B R z U t v) :
    r ∈ v ↔ ∃ a c y p s u q, Entry_d M a c x ∧ M.mem c C ∧ KPair_d M c p s ∧ U p ∧
      Curry_d M B C a y ∧ Qval_d M B R z U y u ∧ Qval_d M B R z U s q ∧ KPair_d E r u q := by
  have coeff c p s (hc : M.mem c C) (hcp : KPair_d M c p s) : M.mem p B ∧ Name_d M B s := by
    obtain ⟨hs, hp, _⟩ := (two_step_mem_l h hcp).mp hc
    exact ⟨hp.1, W, hs, h.closed⟩
  constructor
  · intro hr
    obtain ⟨k, p, hkp, hp, hkr⟩ := (qval_mem_l O hZF hU hv).mp hr
    obtain ⟨a, c, y, s, hac, hc, hcp, hay, hk⟩ :=
      (curry_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) ht k p).mp hkp
    obtain ⟨u, hyu⟩ := name_value_l (R := R) (z := z) (U := U) (curry_name_l M hZF coeff hay)
    obtain ⟨q, hsq⟩ := name_value_l (R := R) (z := z) (U := U) (coeff c p s hc hcp).2
    exact ⟨a, c, y, p, s, u, q, hac, hc, hcp, hp, hay, hyu, hsq, nkpair_val_l O hZF hU hk hyu hsq hkr⟩
  · rintro ⟨a, c, y, p, s, u, q, hac, hc, hcp, hp, hay, hyu, hsq, hr⟩
    obtain ⟨k, hk⟩ := nkpair_l M hZF B y s
    obtain ⟨r', hkr⟩ := name_value_l (R := R) (z := z) (U := U)
      (nkpair_name_l M hZF (qval_name_l hyu) (qval_name_l hsq) hk)
    have he := kpair_unique_l E (extension_ext_l O hZF hU) (nkpair_val_l O hZF hU hk hyu hsq hkr) hr
    exact (qval_mem_l O hZF hU hv).mpr ⟨k, p,
      (curry_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) ht k p).mpr
        ⟨a, c, y, s, hac, hc, hcp, hay, hk⟩, hp, he ▸ hkr⟩

theorem curry_val_entry_l (h : Two_step_d M B R z b A T W C S)
    {x t} (ht : Curry_d M B C x t) {v u q : (E).Domain} (hv : Qval_d M B R z U t v) :
    Entry_d E u q v ↔ ∃ a c y p s, Entry_d M a c x ∧ M.mem c C ∧ KPair_d M c p s ∧ U p ∧
      Curry_d M B C a y ∧ Qval_d M B R z U y u ∧ Qval_d M B R z U s q := by
  constructor
  · rintro ⟨r, hr, hrv⟩
    obtain ⟨a, c, y, p, s, u', q', hac, hc, hcp, hp, hay, hyu, hsq, hr'⟩ :=
      (curry_val_mem_l O hZF hU h ht hv).mp hrv
    obtain ⟨rfl, rfl⟩ := kpair_injective_l E hr hr'
    exact ⟨a, c, y, p, s, hac, hc, hcp, hp, hay, hyu, hsq⟩
  · rintro ⟨a, c, y, p, s, hac, hc, hcp, hp, hay, hyu, hsq⟩
    obtain ⟨r, hr⟩ := (kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)).total u q
    exact ⟨r, hr, (curry_val_mem_l O hZF hU h ht hv).mpr ⟨a, c, y, p, s, u, q, hac, hc, hcp, hp, hay, hyu, hsq, hr⟩⟩

/-- 任意二步名称转换后，在第一泛型扩张内实际成为第二阶段名称。 -/
theorem curry_second_name_l (h : Two_step_d M B R z b A T W C S)
    {x t} (hx : Name_d M C x) (ht : Curry_d M B C x t) {Q v : (E).Domain}
    (hA : Qval_d M B R z U A Q) (hv : Qval_d M B R z U t v) : Name_d E Q v := by
  have coeff c p s (hc : M.mem c C) (hcp : KPair_d M c p s) : M.mem p B ∧ Name_d M B s := by
    obtain ⟨hs, hp, _⟩ := (two_step_mem_l h hcp).mp hc
    exact ⟨hp.1, W, hs, h.closed⟩
  have name {y u} (hu : Curry_d M B C y u) : Name_d M B u := curry_name_l M hZF coeff hu
  obtain ⟨W₀, hxW, hW⟩ := hx
  let ρ : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push C
  let φ : BinarySchema 2 := { body := curry_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ y u : φ.denote ρ y u ↔ Curry_d M B C y u := curry_sat_l M hZF.1 ((ρ.push y).push u) _ _ _ _
  obtain ⟨D, hD'⟩ := ZF.exists_functionalImageOn hZF φ ρ W₀ (fun y _ => by
    obtain ⟨u, hu⟩ := curry_exists_l M hZF B C y
    exact ⟨u, (hφ y u).mpr hu⟩)
    (fun y _ u a hu ha => curry_unique_l M hZF.1 (check_ind_l M hZF) B C y u a ((hφ y u).mp hu) ((hφ y a).mp ha))
  have hD u : M.mem u D ↔ ∃ y, M.mem y W₀ ∧ Curry_d M B C y u := by
    rw [hD' u]
    exact exists_congr fun y => and_congr_right fun _ => hφ y u
  let δ : Env M 0 := ⟨Fin.elim0, fun _ => B⟩
  let ψ : BinarySchema 0 := { body := .truth }
  have hψ u p : ψ.denote δ u p := (Formula.satisfies_truth_iff _).mpr True.intro
  obtain ⟨Z, hZ, _, hZE⟩ := name_comp_l M hZF ψ δ B D (fun u hu => by
    obtain ⟨y, _, hyu⟩ := (hD u).mp hu
    exact name hyu)
  obtain ⟨Y, hY⟩ := name_value_l (R := R) (z := z) (U := U) hZ
  have cover {y u} {a : (E).Domain} (hy : M.mem y W₀) (hu : Curry_d M B C y u)
      (ha : Qval_d M B R z U u a) : a ∈ Y := by
    obtain ⟨p, hp⟩ := hU.inhabited
    exact (qval_mem_l O hZF hU hY).mpr ⟨u, p,
      (hZE u p).mpr ⟨(hD u).mpr ⟨y, hy, hu⟩, (hU.proper p hp).1, hψ u p⟩, hp, ha⟩
  refine ⟨Y, cover hxW ht hv, fun a ha r hra => ?_⟩
  obtain ⟨u, p, hup, _, hua⟩ := (qval_mem_l O hZF hU hY).mp ha
  obtain ⟨y, hyW, hyu⟩ := (hD u).mp ((hZE u p).mp hup).1
  obtain ⟨c, d, u₀, p, s, v₀, q, hcd, hdC, hdp, hp, hcu, hv₀, hq, hr⟩ :=
    (curry_val_mem_l O hZF hU h hyu hua).mp hra
  have hm := ((two_step_mem_l h hdp).mp hdC).2.2
  exact ⟨v₀, q, hr,
    cover (supp_entry_l M hW hyW hcd).1 hcu hv₀,
    (qval_mem_forcing_l O hZF hU hq hA).mp ⟨p, hp, hm⟩⟩

omit hU in
/-- 一次取得唯一转换名称及其对全部首阶段泛型的第二阶段名称证书。 -/
theorem two_step_name_l (h : Two_step_d M B R z b A T W C S) {x} (hx : Name_d M C x) :
    ∃ t, Curry_d M B C x t ∧ Name_d M B t ∧ (∀ s, Curry_d M B C x s → s = t) ∧
      ∀ V, Generic_d M B R z V → ∀ Q v : (extension_l M hZF B R z V).Domain,
        Qval_d M B R z V A Q → Qval_d M B R z V t v → Name_d (extension_l M hZF B R z V) Q v := by
  obtain ⟨t, ht, htN, hu⟩ := two_step_curry_l M hZF h x
  exact ⟨t, ht, htN, hu, fun V hV _ _ hA hv => curry_second_name_l O hZF hV h hx ht hA hv⟩

end YesMetaZFC.Model.Forcing.Internal
