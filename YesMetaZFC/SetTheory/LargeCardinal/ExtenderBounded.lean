import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedSyntax

/-! # 正规性推出有界投影保持

正向在每个源纤维中取最小序数见证，再用正规性把见证变成新坐标。
反向使用坐标序的测度一集合和前缀协调律。统一化只需 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ex_bp_select_l (hZF : M.Models ZF) {κ n i A B D : M.Domain}
    (hκ : M.IsOrdinal κ) (hne : ∃ z, M.mem z κ) (hB : Ex_bp_d κ n i A B) :
    ∃ f, Fn0_d D κ f ∧ ∀ s x, M.mem s B → Rd_entry_d s x f → Ex_bp_at_d κ n i A s x := by
  classical
  obtain ⟨z, hz⟩ := hne
  let ρ := (((((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push n).push i).push A).push B).push z
  let φ : BinarySchema 6 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 3))
      (ex_bp_at_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest))
      (.conj (.neg (.mem (.bound 1) (.bound 3))) (Formula.extensionalEq .newest (.bound 2))) }
  have sat s x : φ.denote ρ s x ↔ (M.mem s B ∧ Ex_bp_at_d κ n i A s x) ∨ (¬ M.mem s B ∧ x = z) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, ex_bp_at_sat_l hZF.1, Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨f, hf, spec⟩ := ZF.ordinal_uniformize_l hZF φ ρ (D := D) hκ
    (fun s _ => by
      by_cases hs : M.mem s B
      · obtain ⟨x, hx⟩ := ((hB s).mp hs).2
        exact ⟨x, (sat s x).mpr (Or.inl ⟨hs, hx⟩)⟩
      · exact ⟨z, (sat s z).mpr (Or.inr ⟨hs, rfl⟩)⟩)
    (fun s x _ hx => ((sat s x).mp hx).elim (fun h => h.2.1) (fun h => h.2 ▸ hz))
  exact ⟨f, hf, fun s x hs hx => ((sat s x).mp (spec s x hx)).elim And.right (fun h => (h.1 hs).elim)⟩

theorem ex_bounded_projection_l (hZF : M.Models ZF) {ω κ L F S n m i A B A' B' : M.Domain}
    (hκ : M.IsOrdinal κ) (hne : ∃ z, M.mem z κ) (hF : Em_family_d ω κ L F)
    (hc : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (normal : En_normal_d ω κ L F) (atoms : Ea_atoms_d ω κ L F)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hn : M.mem n ω) (hm : M.mem m ω) (hsucc : M.SuccessorOf m n) (hi : M.mem i n)
    (hA : ∀ s, M.mem s A → Fn0_d m κ s) (hB : Ex_bp_d κ n i A B)
    (heA : Ex_value_d F S A A') (heB : Ex_value_d F S B B') : Ex_bp_d L n i A' B' := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hBt s (hs : M.mem s B) := ((hB s).mp hs).1
  have hnm : M.MemberSubset n m := fun x hx => (hsucc x).mpr (Or.inl hx)
  intro a
  constructor
  · intro haB
    have ha := ex_value_type_l hZF.1 hF hBt heB a haB
    have haS := ((heB a).mp haB).1
    obtain ⟨U, haU⟩ := hF.total n a hn ha
    have hBU := (ex_value_at_l hZF.1 hF haS ha haU hBt heB).mp haB
    obtain ⟨r, D, _, hr, hD, _⟩ := hF.measure a U haU
    have er := hr.domain_eq_l hZF.1 ha
    subst r
    obtain ⟨f, hf, select⟩ := ex_bp_select_l hZF (D := D) hκ hne hB
    obtain ⟨α, hα, hiα⟩ := ha.2.1 i hi
    have below s (hs : M.mem s B) x y (hsx : Rd_entry_d s x f) (hiy : Rd_entry_d i y s) : M.mem x y := by
      obtain ⟨_, _, _, _, _, y', hy', hiy', hxy⟩ := select s x hs hsx
      exact (hBt s hs).2.2 i hi y' hy' y ((hBt s hs).bound_l hiy).2 hiy' hiy ▸ hxy
    obtain ⟨r, b, V, β, T, hr, hsn, hb, hab, hnβ, hβα, hbV, hTV, graph⟩ :=
      normal n a U D f i α B hn ha haU hD hf hiα hBU below
    have er := Structure.SuccessorOf.eq hZF.1 hsn hsucc
    subst r
    obtain ⟨r, D', _, hr, hD', hV⟩ := hF.measure b V hbV
    have er := hr.domain_eq_l hZF.1 hb
    subst r
    have sub : M.MemberSubset T A := by
      intro s hs
      obtain ⟨t, ht, hts, x, _, htx, hnx⟩ := graph s hs
      obtain ⟨_, u, huA, htu, hnu, _⟩ := select t x ht htx
      have eq := ex_append_unique_l hZF.1 hsucc (hBt t ht) ((hD' s).mp (hV.1.1 T hTV s hs))
        (hA u huA) hts htu hnx hnu
      exact eq.symm ▸ huA
    have hbA := (heA b).mpr ⟨(hS b).mpr ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) hb⟩, V, T, hbV, hTV, sub⟩
    exact ⟨ha, β, (hb.bound_l hnβ).2, b, hbA, hab, hnβ, α, hα, hiα, hβα⟩
  · rintro ⟨ha, β, hβ, b, hbA, hab, hnβ, α, hα, hiα, hβα⟩
    have hb := ex_value_type_l hZF.1 hF hA heA b hbA
    have haS := (hS a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ha⟩
    have hbS := ((heA b).mp hbA).1
    obtain ⟨U, haU⟩ := hF.total n a hn ha
    obtain ⟨V, hbV⟩ := hF.total m b hm hb
    have hAV := (ex_value_at_l hZF.1 hF hbS hb hbV hA heA).mp hbA
    have hbiα : Rd_entry_d i α b := hiα.elim fun p hp => ⟨p, hp.1, hab p hp.2⟩
    obtain ⟨T, hT, ht⟩ := atoms false m b V n i β α hm hb hbV hnβ hbiα
    have hTV : M.mem T V := ht.mpr hβα
    obtain ⟨Z, hz, hZV⟩ := ex_prefix_pull_l hZF hc hn hm hnm ha hb hab haU hbV hBt
    obtain ⟨r, D, _, hr, hD, hV⟩ := hF.measure b V hbV
    have er := hr.domain_eq_l hZF.1 hb
    subst r
    obtain ⟨G, hG, gA, gT⟩ := hV.1.2.2.2 A T hAV hTV
    have sub : M.MemberSubset G Z := by
      intro s hs
      have hsA := gA s hs
      have hsFn := hA s hsA
      obtain ⟨t, ht⟩ := ZF.exists_restriction hZF I s n
      have htf := ht.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) hsFn) hnm
      have hts := (Descriptive.ds_restrict_iff_l I htf (fn0_function_l (ZF.modelsKP hZF) hsFn).1).mp ht
      obtain ⟨x, hx, hnx⟩ := hsFn.2.1 n hsucc.predecessor_mem
      obtain ⟨y, hy, hiy⟩ := htf.2.2 i hi
      have his := ((ht.2 i y).mp hiy).2
      have hxy := (ea_test_read_l false hsFn hnx his).mp (((hT s).mp (gT s hs)).2)
      have htB := (hB t).mpr ⟨fn0_of_function_l (ZF.modelsKP hZF) htf, x, hx, s, hsA, hts, hnx, y, hy, hiy, hxy⟩
      exact (hz s).mpr ⟨hsFn, t, htB, hts⟩
    have hZ := hV.1.2.2.1 G Z hG sub (fun s hs => (hD s).mpr (((hz s).mp hs).1))
    exact (ex_value_at_l hZF.1 hF haS ha haU hBt heB).mpr (hZV.mp hZ)

end YesMetaZFC.SetTheory.LargeCardinal
