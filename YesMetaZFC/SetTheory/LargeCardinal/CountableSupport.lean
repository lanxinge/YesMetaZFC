import YesMetaZFC.SetTheory.Card.CountablePair
import YesMetaZFC.SetTheory.Card.OrdinalImage
import YesMetaZFC.SetTheory.Card.FiniteOrdinal
import YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax
import YesMetaZFC.SetTheory.Card.CantorBernstein
import YesMetaZFC.SetTheory.FunctionRetraction
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 可数个有限支撑的统一坐标列

先把全部坐标写成内部 ω×ω 上的部分求值图，再用最小原像编号压成可数集。
加入 ω 后应用 Cantor–Bernstein，得到不重复且覆盖全部支撑的坐标列；全程只用 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ec_value_d (A p x : M.Domain) : Prop := ∃ n i a,
  KPair_d M p n i ∧ Rd_entry_d n a A ∧ Rd_entry_d i x a

def ec_value_m {d} (A p x : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.conj
  (kpair_m p.weaken.weaken.weaken (.bound 2) (.bound 1)) (.conj
    (rd_entry_m (.bound 2) .newest A.weaken.weaken.weaken)
    (rd_entry_m (.bound 1) x.weaken.weaken.weaken .newest)))))
derive_free_closed ec_value_m

theorem ec_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (A p x : Term d) :
    Formula.satisfies ρ (ec_value_m A p x) ↔ Ec_value_d (A.eval ρ) (p.eval ρ) (x.eval ρ) := by
  simp only [ec_value_m, Ec_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

/-- 显式有限列族的所有坐标可数；不调用“可数个可数集之并”的选择版本。 -/
theorem ec_coordinates_l (hZF : M.Models ZF) {ω L S A : M.Domain} (hω : M.IsOmega ω)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hA : Fn0_d ω S A) :
    ∃ C, M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZF)) C ω ∧
      ∀ x, M.mem x C ↔ ∃ n a i, Rd_entry_d n a A ∧ Rd_entry_d i x a := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 1 := ⟨fun _ => A, fun _ => A⟩
  let φ : BinarySchema 1 := { body := ec_value_m (.bound 2) (.bound 1) .newest }
  have sat p x : φ.denote ρ p x ↔ Ec_value_d A p x := ec_value_sat_l hZF.1 _ _ _ _
  obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I ω ω
  let ψ : UnarySchema 1 := { body := .existsE (ec_value_m (.bound 2) (.bound 1) .newest) }
  obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF ψ ρ W
  have hD p : M.mem p D ↔ M.mem p W ∧ ∃ x, Ec_value_d A p x := by
    simpa only [ψ, Formula.satisfies_exists_iff, ec_value_sat_l hZF.1] using! hd p
  have af := fn0_function_l (ZF.modelsKP hZF) hA
  obtain ⟨E, he, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := L)
    (fun p hp => (((hD p).mp hp).2).imp fun x hx => (sat p x).mpr hx)
    (fun p _ x y hx hy => by
      obtain ⟨n, i, a, hp, hna, hix⟩ := (sat p x).mp hx
      obtain ⟨m, k, b, hp', hmb, hky⟩ := (sat p y).mp hy
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
      have e := af.1.2 n b a hmb hna
      subst b
      obtain ⟨_, _, ha⟩ := (hS a).mp (hA.bound_l hna).2
      exact ha.1.2 i x y hix hky)
    (fun p x _ hx => by
      obtain ⟨n, _, a, _, hna, hix⟩ := (sat p x).mp hx
      obtain ⟨_, _, ha⟩ := (hS a).mp (hA.bound_l hna).2
      exact ha.output_mem_of_pairMember hix)
  obtain ⟨C, hC⟩ := ZF.exists_range_of_setFunction hZF I he.1 he.2.1
  have ef : M.IsSetFunctionFromTo I E D C := ⟨he.1, he.2.1,
    fun p hp => (he.2.2 p hp).imp fun x hx => ⟨(hC x).mpr ⟨p, hx.2⟩, hx.2⟩⟩
  obtain ⟨id, hid⟩ := ZF.exists_identityBijection hZF I ω
  obtain ⟨j, hj⟩ := ZF.countable_product_l I hZF hω ⟨id, hid.1⟩ ⟨id, hid.1⟩ hW
  obtain ⟨k, hk⟩ := ZF.exists_inclusionInjection hZF I (fun p hp => ((hD p).mp hp).1)
  refine ⟨C, ZF.ordinal_image_bound_l I hZF (hω.isOrdinal hZF)
    (ZF.exists_compositionInjection hZF I hk hj) ef (fun x hx => ((hC x).mp hx).imp fun p hp =>
      ⟨he.input_mem_of_pairMember hp, hp⟩), fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := (hC x).mp hx
    obtain ⟨n, i, a, _, hna, hix⟩ := (sat p x).mp ((spec p x).mp hp).2
    exact ⟨n, a, i, hna, hix⟩
  · rintro ⟨n, a, i, hna, hix⟩
    obtain ⟨m, hm, ha⟩ := (hS a).mp (hA.bound_l hna).2
    obtain ⟨p, hp⟩ := I.total n i
    have hv : Ec_value_d A p x := ⟨n, i, a, hp, hna, hix⟩
    have hpD := (hD p).mpr ⟨(hW p).mpr ⟨n, (hA.bound_l hna).1, i,
      hω.transitive hZF m hm i (ha.input_mem_of_pairMember hix), hp⟩, x, hv⟩
    exact (hC x).mpr ⟨p, (spec p x).mpr ⟨hpD, (sat p x).mpr hv⟩⟩

/-- 把任意可数坐标集嵌入一条不重复的内部 ω 列，且保留全部原坐标。 -/
theorem ec_cover_l (hZF : M.Models ZF) {ω L C : M.Domain} (hω : M.IsOmega ω)
    (hωL : M.MemberSubset ω L) (hCL : M.MemberSubset C L)
    (hC : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZF)) C ω) :
    ∃ f, M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) f ω L ∧
      ∀ x, M.mem x C → ∃ n, Rd_entry_d n x f := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨D, hD⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) C ω
  obtain ⟨id, hid⟩ := ZF.exists_identityBijection hZF I ω
  have hDω := ZF.countable_union_two_l I hZF hω hC ⟨id, hid.1⟩ hD
  have hωD := ZF.exists_inclusionInjection hZF I (fun n hn => (hD n).mpr (Or.inr hn))
  obtain ⟨f, hf⟩ := ZF.equinumerous_of_cardinalLessOrEqual hZF I hωD hDω
  have hdL : M.MemberSubset D L := fun x hx => ((hD x).mp hx).elim (hCL x) (hωL x)
  exact ⟨f, ⟨⟨hf.1.1.1, hf.1.1.2.1, fun n hn => (hf.1.1.2.2 n hn).imp fun x hx =>
    ⟨hdL x hx.1, hx.2⟩⟩, hf.1.2⟩,
    fun x hx => (hf.2 x ((hD x).mpr (Or.inl hx))).imp fun _ hn => hn.2⟩

/-- 内部有限定义域的自然数值函数有内部有限界。 -/
theorem ec_finite_bound_l (hZF : M.Models ZF) {ω m q : M.Domain} (hω : M.IsOmega ω)
    (hm : M.mem m ω) (hq : Fn0_d m ω q) : ∃ n, M.mem n ω ∧ Fn0_d m n q := by
  classical
  let I := kp_pair_l (ZF.modelsKP hZF)
  have fn := fn0_function_l (ZF.modelsKP hZF) hq
  obtain ⟨D, hD⟩ := ZF.exists_range_of_setFunction hZF I fn.1 fn.2.1
  have qD : M.IsSetFunctionFromTo I q m D := ⟨fn.1, fn.2.1,
    fun i hi => (fn.2.2 i hi).imp fun x hx => ⟨(hD x).mpr ⟨i, hx.2⟩, hx.2⟩⟩
  obtain ⟨id, hid⟩ := ZF.exists_identityBijection hZF I m
  have fin : Finite_d I ω D := ⟨m, hm, ZF.ordinal_image_bound_l I hZF (hω.members_areOrdinals hZF m hm)
    ⟨id, hid.1⟩ qD (fun x hx => ((hD x).mp hx).imp fun i hi => ⟨fn.input_mem_of_pairMember hi, hi⟩)⟩
  by_cases hn : ∃ x, M.mem x D
  · obtain ⟨k, hk, bound⟩ := ZF.finite_max_l I hZF hω (hω.isOrdinal hZF) fin
      (fun x hx => ((hD x).mp hx).elim fun _ hh => (hq.bound_l hh).2) hn
    obtain ⟨n, hn, hnω⟩ := hω.1.2 k (((hD k).mp hk).elim fun _ hh => (hq.bound_l hh).2)
    exact ⟨n, hnω, hq.retarget_l fun i x hix => ((bound x ((hD x).mpr ⟨i, hix⟩))).elim
      (fun hx => (hn x).mpr (Or.inl hx)) (fun e => e.symm ▸ hn.predecessor_mem)⟩
  · obtain ⟨z, _, hzω⟩ := hω.1.1
    exact ⟨z, hzω, hq.retarget_l fun i x hix => (hn ⟨x, (hD x).mpr ⟨i, hix⟩⟩).elim⟩

end YesMetaZFC.SetTheory.LargeCardinal
