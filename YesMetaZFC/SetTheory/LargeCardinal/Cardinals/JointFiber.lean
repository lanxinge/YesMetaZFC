import YesMetaZFC.SetTheory.Card.CountablePair
import YesMetaZFC.SetTheory.Card.OrdinalImage
import YesMetaZFC.SetTheory.Card.FiniteOrdinal
import YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax
import YesMetaZFC.SetTheory.Card.CantorBernstein
import YesMetaZFC.SetTheory.FunctionRetraction
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition
import YesMetaZFC.SetTheory.Card.FiniteSequenceJoin
import YesMetaZFC.SetTheory.Card.SmallEnumeration
import YesMetaZFC.Model.SetTheory.DirectedSystem.Basic
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.SourceProjection
import YesMetaZFC.SetTheory.Filter.Finite
import YesMetaZFC.SetTheory.Descriptive.Coding.Prefix

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
  refine ⟨C, ZF.ordinal_image_bound_l I hZF (hω.isOrdinal (ZF.modelsKP hZF))
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
      hω.transitive (ZF.modelsKP hZF) m hm i (ha.input_mem_of_pairMember hix), hp⟩, x, hv⟩
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
  have fin : Finite_d I ω D := ⟨m, hm, ZF.ordinal_image_bound_l I hZF (hω.members_areOrdinals (ZF.modelsKP hZF) m hm)
    ⟨id, hid.1⟩ qD (fun x hx => ((hD x).mp hx).imp fun i hi => ⟨fn.input_mem_of_pairMember hi, hi⟩)⟩
  by_cases hn : ∃ x, M.mem x D
  · obtain ⟨k, hk, bound⟩ := ZF.finite_max_l I hZF hω (hω.isOrdinal (ZF.modelsKP hZF)) fin
      (fun x hx => ((hD x).mp hx).elim fun _ hh => (hq.bound_l hh).2) hn
    obtain ⟨n, hn, hnω⟩ := hω.1.2 k (((hD k).mp hk).elim fun _ hh => (hq.bound_l hh).2)
    exact ⟨n, hnω, hq.retarget_l fun i x hix => ((bound x ((hD x).mpr ⟨i, hix⟩))).elim
      (fun hx => (hn x).mpr (Or.inl hx)) (fun e => e.symm ▸ hn.predecessor_mem)⟩
  · obtain ⟨z, _, hzω⟩ := hω.1.1
    exact ⟨z, hzω, hq.retarget_l fun i x hix => (hn ⟨x, (hD x).mpr ⟨i, hix⟩⟩).elim⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部有限支撑的定向索引

索引采用不重复的内部有限列；允许任意排列。支撑包含的坐标映射由目标列的
单射性唯一确定。任意两个支撑均有共同上界，不截断支撑大小或使用标准有限性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ec_factor_l (hZF : M.Models ZF) {m n L a b : M.Domain} (ha : Fn0_d m L a)
    (hb : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) b n L)
    (hc : ∀ i x, Rd_entry_d i x a → ∃ j, Rd_entry_d j x b) :
    ∃ q, Fn0_d m n q ∧ Cp0_d m n L q b a := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 2 := (⟨fun _ => a, fun _ => a⟩ : Env M 1).push b
  let φ : BinarySchema 2 := { body := .existsE (.conj (rd_entry_m (.bound 2) .newest (.bound 4))
    (rd_entry_m (.bound 1) .newest (.bound 3))) }
  have sat i j : φ.denote ρ i j ↔ ∃ x, Rd_entry_d i x a ∧ Rd_entry_d j x b := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨q, hq, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := m) (target := n)
    (fun i hi => by
      obtain ⟨x, _, hix⟩ := ha.2.1 i hi
      obtain ⟨j, hjx⟩ := hc i x hix
      exact ⟨j, (sat i j).mpr ⟨x, hix, hjx⟩⟩)
    (fun i _ j k hj hk => by
      obtain ⟨x, hix, hjx⟩ := (sat i j).mp hj
      obtain ⟨y, hiy, hky⟩ := (sat i k).mp hk
      have e := (fn0_function_l (ZF.modelsKP hZF) ha).1.2 i y x hiy hix
      exact hb.2 j k x hjx (e ▸ hky))
    (fun i j _ hj => ((sat i j).mp hj).elim fun _ hh => hb.1.input_mem_of_pairMember hh.2)
  refine ⟨q, fn0_of_function_l (ZF.modelsKP hZF) hq, ha, fun i hi => ?_⟩
  obtain ⟨j, hj, hij⟩ := hq.2.2 i hi
  obtain ⟨x, hix, hjx⟩ := (sat i j).mp ((spec i j).mp hij).2
  exact ⟨j, hj, x, (ha.bound_l hix).2, hij, hjx, hix⟩

theorem ec_factor_unique_l (hE : Extensional M) {m n L a b q r : M.Domain}
    (hb : ∀ i j x, Rd_entry_d i x b → Rd_entry_d j x b → i = j)
    (hq : Fn0_d m n q) (hr : Fn0_d m n r) (hqa : Cp0_d m n L q b a) (hra : Cp0_d m n L r b a) : q = r := by
  apply hq.ext_l hE hr
  intro i hi
  obtain ⟨j, _, x, hx, hij, hjx, hix⟩ := hqa.2 i hi
  obtain ⟨k, _, y, hy, hik, hky, hiy⟩ := hra.2 i hi
  have e := hqa.1.2.2 i hi y hy x hx hiy hix
  exact ⟨j, hij, hb k j x (e ▸ hky) hjx ▸ hik⟩

theorem ec_prefix_l (hZF : M.Models ZF) {ω m L a f : M.Domain} (hω : M.IsOmega ω) (hm : M.mem m ω)
    (ha : Fn0_d m L a) (hf : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) f ω L)
    (hc : ∀ i x, Rd_entry_d i x a → ∃ j, Rd_entry_d j x f) :
    ∃ n b q, M.mem n ω ∧ M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) b n L ∧
      Fn0_d m n q ∧ Cp0_d m n L q b a ∧ M.MemberSubset b f := by
  obtain ⟨q, hq, hqa⟩ := ec_factor_l hZF ha hf hc
  obtain ⟨n, hn, hqn⟩ := ec_finite_bound_l hZF hω hm hq
  obtain ⟨b, hb⟩ := ZF.exists_restriction hZF (kp_pair_l (ZF.modelsKP hZF)) f n
  have bn := hb.isSetFunctionFromTo hf.1 (hω.transitive (ZF.modelsKP hZF) n hn)
  have bf := fn0_of_function_l (ZF.modelsKP hZF) bn
  refine ⟨n, b, q, hn, ⟨bn, fun i j x hi hj => hf.2 i j x ((hb.2 i x).mp hi).2 ((hb.2 j x).mp hj).2⟩,
    hqn, ⟨ha, fun i hi => ?_⟩,
    (res0_of_restriction_l (ZF.modelsKP hZF) (fn0_of_function_l (ZF.modelsKP hZF) hf.1) hb).1⟩
  obtain ⟨j, _, x, hx, hij, hjx, hix⟩ := hqa.2 i hi
  exact ⟨j, (hqn.bound_l hij).2, x, hx, hij, (hb.2 j x).mpr ⟨(hqn.bound_l hij).2, hjx⟩, hix⟩

theorem ec_join_l (hZF : M.Models ZF) {ω L m n a b : M.Domain} (hω : M.IsOmega ω)
    (hm : M.mem m ω) (hn : M.mem n ω)
    (ha : Fn0_d m L a) (hb : Fn0_d n L b) : ∃ k c q r, M.mem k ω ∧
      M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) c k L ∧
      Fn0_d m k q ∧ Cp0_d m k L q c a ∧ Fn0_d n k r ∧ Cp0_d n k L r c b := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨l, d, hl, _, hd, had, hbd⟩ := ZF.fseq_join_l I hZF hω hm hn
    (fn0_function_l (ZF.modelsKP hZF) ha) (fn0_function_l (ZF.modelsKP hZF) hb)
  obtain ⟨D, hD⟩ := ZF.exists_range_of_setFunction hZF I hd.1 hd.2.1
  have dD : M.IsSetFunctionFromTo I d l D := ⟨hd.1, hd.2.1,
    fun i hi => (hd.2.2 i hi).imp fun x hx => ⟨(hD x).mpr ⟨i, hx.2⟩, hx.2⟩⟩
  obtain ⟨id, hid⟩ := ZF.exists_identityBijection hZF I l
  have finite := ZF.ordinal_image_bound_l I hZF (hω.members_areOrdinals (ZF.modelsKP hZF) l hl)
    ⟨id, hid.1⟩ dD (fun x hx => ((hD x).mp hx).imp fun i hi => ⟨hd.input_mem_of_pairMember hi, hi⟩)
  -- 只枚举两支撑的有限并集，不要求支撑字母表包含背景 ω。
  obtain ⟨k, c, hk, _, bij⟩ := ZF.small_enumeration_l I hZF (ZF.omega_cardinal_l I hZF hω) hl finite
  have sub : M.MemberSubset D L := fun x hx => ((hD x).mp hx).elim fun _ hi => hd.output_mem_of_pairMember hi
  have hc : M.IsSetInjectionFromTo I c k L :=
    ⟨fn0_function_l (ZF.modelsKP hZF) ((fn0_of_function_l (ZF.modelsKP hZF) bij.1.1).mono_target_l sub), bij.1.2⟩
  have covered i x (hix : Rd_entry_d i x d) : ∃ j, Rd_entry_d j x c :=
    (bij.2 x ((hD x).mpr ⟨i, hix⟩)).imp fun _ h => h.2
  obtain ⟨q, hq, hqa⟩ := ec_factor_l hZF ha hc (fun i x hi => covered i x ((had.2 i x).mp hi).2)
  obtain ⟨r, hr, hrb⟩ := ec_factor_l hZF hb hc (fun i x hi => by
    obtain ⟨_, j, _, hjx⟩ := (hbd.2 i x).mp hi
    exact covered j x hjx)
  exact ⟨k, c, q, r, hk, hc, hq, hqa, hr, hrb⟩

def Ei_d (ω L a : M.Domain) : Prop := ∃ n, M.mem n ω ∧ Fn0_d n L a ∧
  ∀ i j x, Rd_entry_d i x a → Rd_entry_d j x a → i = j

def ei_m {d} (ω L a : Term d) : Formula 1 d := Formula.existsMem ω
  (.conj (fn0_m .newest L.weaken a.weaken) (Formula.forallMem .newest (Formula.forallMem (.bound 1)
    (Formula.forallMem L.weaken.weaken.weaken (.imp
      (rd_entry0_m (.bound 2) .newest a.weaken.weaken.weaken.weaken) (.imp
        (rd_entry0_m (.bound 1) .newest a.weaken.weaken.weaken.weaken) (Formula.extensionalEq (.bound 2) (.bound 1))))))))
derive_free_closed ei_m

theorem ei_delta_l {d} (ω L a : Term d) : (ei_m ω L a).IsDelta0 :=
  .existsMem _ (.conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.atom ..)))))))

theorem ei_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω L a : Term d) :
    Formula.satisfies ρ (ei_m ω L a) ↔ Ei_d (ω.eval ρ) (L.eval ρ) (a.eval ρ) := by
  simp only [ei_m, Ei_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hE,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]
  exact exists_congr fun n => and_congr_right fun _ =>
    ⟨fun ⟨fn, inj⟩ => ⟨fn, fun i j x hi hj => inj i (fn.bound_l hi).1 j (fn.bound_l hj).1 x (fn.bound_l hi).2 hi hj⟩,
      fun ⟨fn, inj⟩ => ⟨fn, fun i _ j _ x _ => inj i j x⟩⟩

def Ei_map_d (ω L a b q : M.Domain) : Prop := ∃ m n, M.mem m ω ∧ M.mem n ω ∧
  Fn0_d m n q ∧ Fn0_d n L b ∧ Cp0_d m n L q b a

def ei_map_m {d} (ω L a b q : Term d) : Formula 1 d := Formula.existsMem ω (Formula.existsMem ω.weaken
  (.conj (fn0_m (.bound 1) .newest q.weaken.weaken) (.conj (fn0_m .newest L.weaken.weaken b.weaken.weaken)
    (cp0_m (.bound 1) .newest L.weaken.weaken q.weaken.weaken b.weaken.weaken a.weaken.weaken))))
derive_free_closed ei_map_m

theorem ei_map_delta_l {d} (ω L a b q : Term d) : (ei_map_m ω L a b q).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (fn0_delta_l ..) (.conj (fn0_delta_l ..) (cp0_delta_l ..))))

theorem ei_map_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω L a b q : Term d) :
    Formula.satisfies ρ (ei_map_m ω L a b q) ↔
      Ei_map_d (ω.eval ρ) (L.eval ρ) (a.eval ρ) (b.eval ρ) (q.eval ρ) := by
  simp only [ei_map_m, Ei_map_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hE, cp0_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨m, hm, n, hn, h⟩ => ⟨m, n, hm, hn, h⟩, fun ⟨m, n, hm, hn, h⟩ => ⟨m, hm, n, hn, h⟩⟩

theorem ei_order_l (hZF : M.Models ZF) {ω L : M.Domain} (hω : M.IsOmega ω) :
    ∃ J O, (∀ a, M.mem a J ↔ Ei_d ω L a) ∧ Di_order_d J O ∧
      ∀ a b, Rd_entry_d a b O ↔ M.mem a J ∧ M.mem b J ∧ ∃ q, Ei_map_d ω L a b q := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨S, hS⟩ := ZF.fseq_space_exists_l I hZF hω L
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push L
  let φ : UnarySchema 2 := { body := ei_m (.bound 2) (.bound 1) .newest }
  obtain ⟨J, hj⟩ := ZF.separation_exists_d hZF φ ρ S
  have hJ a : M.mem a J ↔ Ei_d ω L a := (hj a).trans
    ((and_congr_right fun _ => ei_sat_l hZF.1 _ _ _ _).trans
      ⟨And.right, fun h => ⟨(hS a).mpr (h.elim fun n hn => ⟨n, hn.1, fn0_function_l (ZF.modelsKP hZF) hn.2.1⟩), h⟩⟩)
  let ψ : BinarySchema 2 := { body := .existsE (ei_map_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  obtain ⟨O, _, ho⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ ρ J
  have spec a b : Rd_entry_d a b O ↔ M.mem a J ∧ M.mem b J ∧ ∃ q, Ei_map_d ω L a b q := by
    simpa only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, ei_map_sat_l hZF.1] using! ho a b
  refine ⟨J, O, hJ, ⟨?_, ?_, fun a b h => ⟨((spec a b).mp h).1, ((spec a b).mp h).2.1⟩, ?_⟩, spec⟩
  · intro a ha
    obtain ⟨m, hm, hma, inj⟩ := (hJ a).mp ha
    obtain ⟨q, hq, hc⟩ := ec_factor_l hZF hma ⟨fn0_function_l (ZF.modelsKP hZF) hma, inj⟩
      (fun i _ hi => ⟨i, hi⟩)
    exact (spec a a).mpr ⟨ha, ha, q, m, m, hm, hm, hq, hma, hc⟩
  · intro a b c hab hbc
    obtain ⟨ha, hb, q, m, n, hm, hn, hq, hnb, hqa⟩ := (spec a b).mp hab
    obtain ⟨_, hc, r, n', l, hn', hl, hr, hlc, hrb⟩ := (spec b c).mp hbc
    have e := hrb.1.domain_eq_l hZF.1 hnb
    subst n'
    obtain ⟨s, hs⟩ := cp0_exists_l (ZF.modelsKP hZF) hq hr
    exact (spec a c).mpr ⟨ha, hc, s, m, l, hm, hl, hs.1, hlc,
      Cp0_d.assoc_l hr hq hs hlc hrb hqa⟩
  · intro a b ha hb
    obtain ⟨m, hm, hma, _⟩ := (hJ a).mp ha
    obtain ⟨n, hn, hnb, _⟩ := (hJ b).mp hb
    obtain ⟨k, c, q, r, hk, hkc, hq, hqa, hr, hrb⟩ := ec_join_l hZF hω hm hn hma hnb
    have hc := (hJ c).mpr ⟨k, hk, fn0_of_function_l (ZF.modelsKP hZF) hkc.1, hkc.2⟩
    exact ⟨c, hc, (spec a c).mpr ⟨ha, hc, q, m, k, hm, hk, hq,
      fn0_of_function_l (ZF.modelsKP hZF) hkc.1, hqa⟩,
      (spec b c).mpr ⟨hb, hc, r, n, k, hn, hk, hr, fn0_of_function_l (ZF.modelsKP hZF) hkc.1, hrb⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限支撑测度的共同约束

约束沿唯一坐标映射拉回；无包含关系时约束为空。有限多个约束的共同细化
仍为测度一，不借用各分量的可数完备性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

structure Em_family_d (ω κ L F : M.Domain) : Prop where
  total : ∀ n a, M.mem n ω → Fn0_d n L a → ∃ U, Rd_entry_d a U F
  function : ∀ a U V, Rd_entry_d a U F → Rd_entry_d a V F → U = V
  measure : ∀ a U, Rd_entry_d a U F → ∃ n D, M.mem n ω ∧ Fn0_d n L a ∧
    (∀ s, M.mem s D ↔ Fn0_d n κ s) ∧ Maximal_d (ℳ := M) D U

theorem Em_family_d.at_l (hE : Extensional M) {ω κ L F a U n D : M.Domain}
    (h : Em_family_d ω κ L F) (ha : Rd_entry_d a U F) (hn : Fn0_d n L a)
    (hD : ∀ s, M.mem s D ↔ Fn0_d n κ s) : Maximal_d (ℳ := M) D U := by
  obtain ⟨m, E, _, hm, he, hu⟩ := h.measure a U ha
  have en := hm.domain_eq_l hE hn
  subst m
  exact hE.eq_of_same_members E D (fun s => (he s).trans (hD s).symm) ▸ hu

/-- 已构造的派生测度族给出不提原嵌入的测度族接口。 -/
theorem es_measures_l (hZF : M.Models ZF) {ω δ X C Y E j κ k L S F : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X C Y E j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k) (hL : M.MemberSubset L k)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hSY : M.MemberSubset S Y)
    (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F) : Em_family_d ω κ L F := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  refine ⟨fun n a hn ha => (hF.2.1 a).mp ((hS a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ha⟩),
    hF.1.2, fun a U ha => ?_⟩
  obtain ⟨n, D, hn, hD, _, hu, _⟩ := es_family_ultra_l I hZF hω hX hδ h hY hc hL hS hSY hF ha
  obtain ⟨m, hm, hma⟩ := (hS a).mp ((hF.2.2 a U).mp ha).1
  have e := (fn0_of_function_l (ZF.modelsKP hZF) hma).domain_eq_l hZF.1 hn
  exact ⟨n, D, e ▸ hm, hn, hD, hu⟩

def Ec_ok_d (κ L a c E s : M.Domain) : Prop := ∀ m n q, Fn0_d m n q → Fn0_d n L c →
  Cp0_d m n L q c a → ∃ r, M.mem r E ∧ Cp0_d m n κ q s r

def ec_ok_m {d} (κ L a c E s : Term d) : Formula 1 d := .forallE (.forallE (.forallE
  (.imp (fn0_m (.bound 2) (.bound 1) .newest) (.imp (fn0_m (.bound 1) L.weaken.weaken.weaken c.weaken.weaken.weaken)
    (.imp (cp0_m (.bound 2) (.bound 1) L.weaken.weaken.weaken .newest c.weaken.weaken.weaken a.weaken.weaken.weaken)
      (Formula.existsMem E.weaken.weaken.weaken (cp0_m (.bound 3) (.bound 2) κ.weaken.weaken.weaken.weaken
        (.bound 1) s.weaken.weaken.weaken.weaken .newest)))))))
derive_free_closed ec_ok_m

theorem ec_ok_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L a c E s : Term d) :
    Formula.satisfies ρ (ec_ok_m κ L a c E s) ↔
      Ec_ok_d (κ.eval ρ) (L.eval ρ) (a.eval ρ) (c.eval ρ) (E.eval ρ) (s.eval ρ) := by
  simp only [ec_ok_m, Ec_ok_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    fn0_sat_l hE, cp0_sat_l hE, Formula.satisfies_existsMem_iff, Definitional.Term.eval_weaken]; rfl

theorem ec_ok_iff_l (hE : Extensional M) {κ L m n a c E s q : M.Domain}
    (hc : Fn0_d n L c) (hinj : ∀ i j x, Rd_entry_d i x c → Rd_entry_d j x c → i = j)
    (hq : Fn0_d m n q) (ha : Cp0_d m n L q c a) :
    Ec_ok_d κ L a c E s ↔ ∃ r, M.mem r E ∧ Cp0_d m n κ q s r := by
  refine ⟨fun h => h m n q hq hc ha, fun h m' n' q' hq' hc' ha' => ?_⟩
  have e := hc'.domain_eq_l hE hc
  subst n'
  have e := ha'.1.domain_eq_l hE ha.1
  subst m'
  exact ec_factor_unique_l hE hinj hq hq' ha ha' ▸ h

/-- 一个有限支撑约束在任意包含它的单射支撑上仍为测度一。 -/
theorem ec_test_l (hZF : M.Models ZF) {ω κ L F m n a c U V E D : M.Domain}
    (hco : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (hm : M.mem m ω) (hn : M.mem n ω) (ha : Fn0_d m L a) (hc : Fn0_d n L c)
    (hinj : ∀ i j x, Rd_entry_d i x c → Rd_entry_d j x c → i = j)
    (hU : Rd_entry_d a U F) (hV : Rd_entry_d c V F) (hEV : M.mem E U)
    (hE : ∀ r, M.mem r E → Fn0_d m κ r) (hD : ∀ s, M.mem s D ↔ Fn0_d n κ s)
    (hVD : IsFilter_d (ℳ := M) D V) : ∃ B, M.mem B V ∧
      ∀ s, M.mem s B ↔ M.mem s D ∧ Ec_ok_d κ L a c E s := by
  classical
  by_cases refines : ∃ q, Fn0_d m n q ∧ Cp0_d m n L q c a
  · obtain ⟨q, hq, hqa⟩ := refines
    obtain ⟨B, hB, hu⟩ := hco m n q c a U V E hm hn hq hc hqa hV hU hE
    exact ⟨B, hu.mpr hEV, fun s => (hB s).trans
      (and_congr (hD s).symm (ec_ok_iff_l hZF.1 hc hinj hq hqa).symm)⟩
  · refine ⟨D, hVD.2.1, fun s => ⟨fun hs => ⟨hs, ?_⟩, And.left⟩⟩
    intro m' n' q hq hc' hqa
    have en := hc'.domain_eq_l hZF.1 hc
    subst n'
    have em := hqa.1.domain_eq_l hZF.1 ha
    subst m'
    exact (refines ⟨q, hq, hqa⟩).elim

def Ec_all_d (κ L A B n c s : M.Domain) : Prop := ∀ i a E, M.mem i n →
  Rd_entry_d i a A → Rd_entry_d i E B → Ec_ok_d κ L a c E s

def ec_all_m {d} (κ L A B n c s : Term d) : Formula 1 d := .forallE (.forallE (.forallE
  (.imp (.mem (.bound 2) n.weaken.weaken.weaken) (.imp (rd_entry_m (.bound 2) (.bound 1) A.weaken.weaken.weaken)
    (.imp (rd_entry_m (.bound 2) .newest B.weaken.weaken.weaken)
      (ec_ok_m κ.weaken.weaken.weaken L.weaken.weaken.weaken (.bound 1) c.weaken.weaken.weaken .newest s.weaken.weaken.weaken))))))
derive_free_closed ec_all_m

theorem ec_all_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L A B n c s : Term d) :
    Formula.satisfies ρ (ec_all_m κ L A B n c s) ↔
      Ec_all_d (κ.eval ρ) (L.eval ρ) (A.eval ρ) (B.eval ρ) (n.eval ρ) (c.eval ρ) (s.eval ρ) := by
  simp only [ec_all_m, Ec_all_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, rd_entry_sat_l hE, ec_ok_sat_l hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共同纤维所需的实际层族

第 n 层同时检验前 n 个已经能在当前支撑中读取的约束。测度一只由有限交
推出；整个 ω 层族由唯一值收集生成，供既有共同纤维定理直接调用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

theorem ec_meet_l (hZF : M.Models ZF) {ω κ L F S P A B n c U D : M.Domain}
    (hω : M.IsOmega ω) (hF : Em_family_d ω κ L F)
    (hco : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hA : Fn0_d ω S A) (hB : Fn0_d ω P B)
    (large : ∀ i a E V, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a V F → M.mem E V)
    (hn : M.mem n ω) (hc : Fn0_d n L c)
    (hinj : ∀ i j x, Rd_entry_d i x c → Rd_entry_d j x c → i = j)
    (hU : Rd_entry_d c U F) (hD : ∀ s, M.mem s D ↔ Fn0_d n κ s) (hu : IsFilter_d (ℳ := M) D U) :
    ∃ C, M.mem C U ∧ ∀ s, M.mem s C ↔ M.mem s D ∧ Ec_all_d κ L A B n c s := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ := (((((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push L).push A).push B).push c).push D
  let φ : BinarySchema 6 := { body := .existsE (.existsE (.conj
    (rd_entry_m (.bound 3) (.bound 1) (.bound 7)) (.conj (rd_entry_m (.bound 3) .newest (.bound 6))
      (.forallE (.iff (.mem .newest (.bound 3)) (.conj (.mem .newest (.bound 5))
        (ec_ok_m (.bound 10) (.bound 9) (.bound 2) (.bound 6) (.bound 1) .newest))))))) }
  have sat i Z : φ.denote ρ i Z ↔ ∃ a E, Rd_entry_d i a A ∧ Rd_entry_d i E B ∧
      ∀ s, M.mem s Z ↔ M.mem s D ∧ Ec_ok_d κ L a c E s := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, ec_ok_sat_l hZF.1]; rfl
  have member i Z (hi : M.mem i n) (hz : φ.denote ρ i Z) : M.mem Z U := by
    obtain ⟨a, E, hia, hiE, hz⟩ := (sat i Z).mp hz
    obtain ⟨m, hm, hma⟩ := (hS a).mp (hA.bound_l hia).2
    obtain ⟨V, haV⟩ := hF.total m a hm (fn0_of_function_l (ZF.modelsKP hZF) hma)
    obtain ⟨m', D', _, hma', hd', hv⟩ := hF.measure a V haV
    have e := hma'.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hma)
    subst m'
    obtain ⟨Z', hZ', hz'⟩ := ec_test_l hZF hco hm hn (fn0_of_function_l (ZF.modelsKP hZF) hma) hc hinj
      haV hU (large i a E V hia hiE haV)
      (fun r hr => (hd' r).mp (hv.1.1 E (large i a E V hia hiE haV) r hr)) hD hu
    exact (hZF.1.eq_of_same_members Z' Z (fun s => (hz' s).trans (hz s).symm)) ▸ hZ'
  obtain ⟨H, hh, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := U)
    (fun i hi => by
      have hiω := hω.transitive (ZF.modelsKP hZF) n hn i hi
      obtain ⟨a, _, hia⟩ := hA.2.1 i hiω
      obtain ⟨E, _, hiE⟩ := hB.2.1 i hiω
      let ψ : UnarySchema 5 := { body := ec_ok_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
      obtain ⟨Z, hz⟩ := ZF.separation_exists_d hZF ψ
        ⟨Fin.cases E (Fin.cases c (Fin.cases a (Fin.cases L (fun _ => κ)))), fun _ => κ⟩ D
      exact ⟨Z, (sat i Z).mpr ⟨a, E, hia, hiE,
        fun s => (hz s).trans (and_congr_right fun _ => ec_ok_sat_l hZF.1 _ _ _ _ _ _ _)⟩⟩)
    (fun i _ Z W hz hw => by
      obtain ⟨a, E, hia, hiE, hz⟩ := (sat i Z).mp hz
      obtain ⟨a', E', hia', hiE', hw⟩ := (sat i W).mp hw
      have e := (fn0_function_l (ZF.modelsKP hZF) hA).1.2 i a' a hia' hia
      subst a'
      have e := (fn0_function_l (ZF.modelsKP hZF) hB).1.2 i E' E hiE' hiE
      subst E'
      exact hZF.1.eq_of_same_members Z W fun s => (hz s).trans (hw s).symm) member
  obtain ⟨K, hKU, hk⟩ := finite_meet_l hZF hω hu.base_l n hn H (fn0_of_function_l (ZF.modelsKP hZF) hh)
  let η := (((((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push L).push A).push B).push n).push c
  let ψ : UnarySchema 6 := { body := ec_all_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hc'⟩ := ZF.separation_exists_d hZF ψ η D
  have specC s : M.mem s C ↔ M.mem s D ∧ Ec_all_d κ L A B n c s :=
    (hc' s).trans (and_congr_right fun _ => ec_all_sat_l hZF.1 _ _ _ _ _ _ _ _)
  refine ⟨C, hu.2.2.1 K C hKU (fun s hs => (specC s).mpr ⟨hu.1 K hKU s hs, ?_⟩)
    (fun s hs => ((specC s).mp hs).1), specC⟩
  intro i a E hi hia hiE
  obtain ⟨Z, _, hiZ⟩ := hh.2.2 i hi
  obtain ⟨a', E', hia', hiE', hz⟩ := (sat i Z).mp ((spec i Z).mp hiZ).2
  have e := (fn0_function_l (ZF.modelsKP hZF) hA).1.2 i a' a hia' hia
  subst a'
  have e := (fn0_function_l (ZF.modelsKP hZF) hB).1.2 i E' E hiE' hiE
  subst E'
  exact ((hz s).mp (hk i Z hi hiZ s hs)).2

def Ec_level_d (κ L A B f n C : M.Domain) : Prop := ∀ s, M.mem s C ↔ Fn0_d n κ s ∧
  ∀ c, Fn0_d n L c → M.MemberSubset c f → Ec_all_d κ L A B n c s

def ec_level_m {d} (κ L A B f n C : Term d) : Formula 1 d := .forallE (.iff (.mem .newest C.weaken)
  (.conj (fn0_m n.weaken κ.weaken .newest) (.forallE (.imp (fn0_m n.weaken.weaken L.weaken.weaken .newest)
    (.imp (Formula.subset .newest f.weaken.weaken)
      (ec_all_m κ.weaken.weaken L.weaken.weaken A.weaken.weaken B.weaken.weaken n.weaken.weaken .newest (.bound 1)))))))
derive_free_closed ec_level_m

theorem ec_level_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L A B f n C : Term d) :
    Formula.satisfies ρ (ec_level_m κ L A B f n C) ↔
      Ec_level_d (κ.eval ρ) (L.eval ρ) (A.eval ρ) (B.eval ρ) (f.eval ρ) (n.eval ρ) (C.eval ρ) := by
  simp only [ec_level_m, Ec_level_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, ec_all_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ec_levels_l (hZF : M.Models ZF) {ω κ L F S P A B f : M.Domain}
    (hω : M.IsOmega ω) (hF : Em_family_d ω κ L F)
    (hco : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hA : Fn0_d ω S A) (hB : Fn0_d ω P B)
    (large : ∀ i a E U, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a U F → M.mem E U)
    (hf : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) f ω L) :
    ∃ H, Ef_levels_d ω κ H ∧ Es_fiber_d (kp_pair_l (ZF.modelsKP hZF)) ω L F H f ∧
      ∀ n C, Rd_entry_d n C H → Ec_level_d κ L A B f n C := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω κ
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF K
  let ρ := ((((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push L).push A).push B).push f
  let φ : BinarySchema 5 := { body := ec_level_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat n C : φ.denote ρ n C ↔ Ec_level_d κ L A B f n C := ec_level_sat_l hZF.1 _ _ _ _ _ _ _ _
  obtain ⟨H, hh, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := Q)
    (fun n hn => by
      let ψ : UnarySchema 6 := { body := .forallE (.imp (fn0_m (.bound 2) (.bound 6) .newest)
        (.imp (Formula.subset .newest (.bound 3))
          (ec_all_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 2) .newest (.bound 1)))) }
      obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF I n κ
      obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF ψ (ρ.push n) D
      refine ⟨C, (sat n C).mpr fun s => (hC s).trans ?_⟩
      have hs : ψ.denote (ρ.push n) s ↔ ∀ c, Fn0_d n L c → M.MemberSubset c f → Ec_all_d κ L A B n c s := by
        simp only [ψ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
          fn0_sat_l hZF.1, Formula.satisfies_subset_iff, ec_all_sat_l hZF.1]; rfl
      exact and_congr ((hD s).trans ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩) hs)
    (fun n _ C D hc hd => hZF.1.eq_of_same_members C D fun s => ((sat n C).mp hc s).trans ((sat n D).mp hd s).symm)
    (fun n C hn hc => (hQ C).mpr fun s hs => (hK s).mpr ⟨n, hn,
      fn0_function_l (ZF.modelsKP hZF) (((sat n C).mp hc s).mp hs).1⟩)
  have levels n C (hnC : Rd_entry_d n C H) := (sat n C).mp ((spec n C).mp hnC).2
  refine ⟨H, ⟨⟨Q, fn0_of_function_l (ZF.modelsKP hZF) hh⟩, fun n C hnC s hs => ((levels n C hnC s).mp hs).1⟩,
    ⟨fn0_of_function_l (ZF.modelsKP hZF) hf.1, fun n hn => ?_⟩, levels⟩
  obtain ⟨c, hc, hcf, _⟩ := Descriptive.ds_prefix_l I hZF hω hf.1 hn
  have sub := (Descriptive.ds_restrict_iff_l I hc hf.1.1).mp hcf
  obtain ⟨U, hcU⟩ := hF.total n c hn (fn0_of_function_l (ZF.modelsKP hZF) hc)
  obtain ⟨n', D, _, hc', hD, hu⟩ := hF.measure c U hcU
  have en := hc'.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hc)
  subst n'
  obtain ⟨C, hCU, hs⟩ := ec_meet_l hZF hω hF hco hS hA hB large hn hc'
    (fun i j x hi hj => hf.2 i j x ((hcf.2 i x).mp hi).2 ((hcf.2 j x).mp hj).2) hcU hD hu.1
  obtain ⟨Z, _, hnZ⟩ := hh.2.2 n hn
  have e : Z = C := by
    apply hZF.1.eq_of_same_members Z C
    intro s
    refine (levels n Z hnZ s).trans ((and_congr (hD s).symm ?_).trans (hs s).symm)
    refine ⟨fun hall => hall c hc' sub, fun hall d hd hdf => ?_⟩
    have eq := ((Descriptive.ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hZF) hd) hf.1.1).mpr hdf).eq hZF.1 hcf
    exact eq.symm ▸ hall
  exact ⟨Z, c, U, hnZ, hc', sub, hcU, e.symm ▸ hCU⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共同纤维同时实现全部可数有限支撑约束

一个共同的单射坐标列和一个 κ 值列同时解释所有支撑，且解释与坐标投影
交换。这里允许可数列中的支撑大小无界；没有把有限定向性改成可数定向性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ec_eval_d (ω κ L f g a r : M.Domain) : Prop := ∃ m q, Fn0_d m ω q ∧
  Cp0_d m ω L q f a ∧ Cp0_d m ω κ q g r

def ec_eval_m {d} (ω κ L f g a r : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (fn0_m (.bound 1) ω.weaken.weaken .newest)
    (.conj (cp0_m (.bound 1) ω.weaken.weaken L.weaken.weaken .newest f.weaken.weaken a.weaken.weaken)
      (cp0_m (.bound 1) ω.weaken.weaken κ.weaken.weaken .newest g.weaken.weaken r.weaken.weaken))))
derive_free_closed ec_eval_m

theorem ec_eval_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L f g a r : Term d) :
    Formula.satisfies ρ (ec_eval_m ω κ L f g a r) ↔
      Ec_eval_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (f.eval ρ) (g.eval ρ) (a.eval ρ) (r.eval ρ) := by
  simp only [ec_eval_m, Ec_eval_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hE, cp0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ec_eval_exists_l (hZF : M.Models ZF) {ω κ L m f g a : M.Domain} (ha : Fn0_d m L a)
    (hf : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) f ω L) (hg : Fn0_d ω κ g)
    (cover : ∀ i x, Rd_entry_d i x a → ∃ j, Rd_entry_d j x f) : ∃ r, Ec_eval_d ω κ L f g a r := by
  obtain ⟨q, hq, hqa⟩ := ec_factor_l hZF ha hf cover
  obtain ⟨r, hr⟩ := cp0_exists_l (ZF.modelsKP hZF) hq hg
  exact ⟨r, m, q, hq, hqa, hr⟩

theorem ec_eval_unique_l (hE : Extensional M) {ω κ L f g a r s : M.Domain}
    (hf : ∀ i j x, Rd_entry_d i x f → Rd_entry_d j x f → i = j) (hg : Fn0_d ω κ g)
    (hr : Ec_eval_d ω κ L f g a r) (hs : Ec_eval_d ω κ L f g a s) : r = s := by
  obtain ⟨m, q, hq, hqa, hqr⟩ := hr
  obtain ⟨n, t, ht, hta, hts⟩ := hs
  have e := hta.1.domain_eq_l hE hqa.1
  subst n
  have e := ec_factor_unique_l hE hf ht hq hta hqa
  subst t
  exact cp0_unique_l hE hq hg hqr hts

theorem ec_eval_type_l (hE : Extensional M) {ω κ L f g a r n : M.Domain}
    (ha : Fn0_d n L a) (hr : Ec_eval_d ω κ L f g a r) : Fn0_d n κ r := by
  obtain ⟨m, _, _, hm, ht⟩ := hr
  exact hm.1.domain_eq_l hE ha ▸ ht.1

theorem ec_eval_comp_l (hKP : M.Models KP) {ω κ L f g a c r s m n q : M.Domain}
    (hf : Fn0_d ω L f) (hg : Fn0_d ω κ g) (hc : Fn0_d n L c) (hq : Fn0_d m n q)
    (hqa : Cp0_d m n L q c a) (hrs : Cp0_d m n κ q s r) (he : Ec_eval_d ω κ L f g c s) :
    Ec_eval_d ω κ L f g a r := by
  obtain ⟨n', t, ht, htc, hts⟩ := he
  have e := htc.1.domain_eq_l hKP.1 hc
  subst n'
  obtain ⟨u, hu⟩ := cp0_exists_l hKP hq ht
  exact ⟨m, u, hu.1, Cp0_d.assoc_l ht hq hu hf htc hqa, Cp0_d.assoc_l ht hq hu hg hts hrs⟩

theorem ec_late_bound_l (hZF : M.Models ZF) {ω i k : M.Domain} (hω : M.IsOmega ω)
    (hi : M.mem i ω) (hk : M.mem k ω) : ∃ n, M.mem n ω ∧ M.mem i n ∧ M.MemberSubset k n := by
  obtain ⟨s, hs, hsω⟩ := hω.1.2 i hi
  rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare k hk s hsω with e | hks | hsk
  · exact ⟨s, hsω, hs.predecessor_mem, fun x hx => (e x).mp hx⟩
  · exact ⟨s, hsω, hs.predecessor_mem, (hω.members_areOrdinals (ZF.modelsKP hZF) s hsω).transitive k hks⟩
  · exact ⟨k, hk, (hω.members_areOrdinals (ZF.modelsKP hZF) k hk).transitive s hsk i hs.predecessor_mem, fun _ => id⟩

/-- 在足够长的共同层读取任意指定约束；只使用已经构造的层族与纤维。 -/
theorem ec_levels_realize_l (hZF : M.Models ZF) {ω κ L S A B f g H : M.Domain}
    (hω : M.IsOmega ω) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hA : Fn0_d ω S A)
    (hf : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) f ω L)
    (covered : ∀ i a j x, Rd_entry_d i a A → Rd_entry_d j x a → ∃ n, Rd_entry_d n x f)
    (fiber : Ef_fiber_d ω κ H g) (read : ∀ n C, Rd_entry_d n C H → Ec_level_d κ L A B f n C) :
    ∀ i a E, Rd_entry_d i a A → Rd_entry_d i E B → ∃ r, M.mem r E ∧ Ec_eval_d ω κ L f g a r := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro i a E hia hiE
  obtain ⟨m, hm, hma⟩ := (hS a).mp (hA.bound_l hia).2
  obtain ⟨q, hq, hqa⟩ := ec_factor_l hZF (fn0_of_function_l (ZF.modelsKP hZF) hma) hf (covered i a · · hia)
  obtain ⟨k, hk, hqk⟩ := ec_finite_bound_l hZF hω hm hq
  obtain ⟨n, hn, hin, hkn⟩ := ec_late_bound_l hZF hω (hA.bound_l hia).1 hk
  have hqn := hqk.mono_target_l hkn
  obtain ⟨c, hc, hcf, _⟩ := Descriptive.ds_prefix_l I hZF hω hf.1 hn
  have hqc : Cp0_d m n L q c a := ⟨hqa.1, fun j hj => by
    obtain ⟨k, _, x, hx, hjk, hkx, hjx⟩ := hqa.2 j hj
    exact ⟨k, (hqn.bound_l hjk).2, x, hx, hjk, (hcf.2 k x).mpr ⟨(hqn.bound_l hjk).2, hkx⟩, hjx⟩⟩
  obtain ⟨Z, s, hnZ, hsZ, hs, hsg⟩ := fiber.2 n hn
  have ok := ((read n Z hnZ s).mp hsZ).2 c (fn0_of_function_l (ZF.modelsKP hZF) hc)
    ((Descriptive.ds_restrict_iff_l I hc hf.1.1).mp hcf) i a E hin hia hiE
  obtain ⟨r, hrE, hsr⟩ := ok m n q hqn (fn0_of_function_l (ZF.modelsKP hZF) hc) hqc
  refine ⟨r, hrE, m, q, hq, hqa, hsr.1, fun j hj => ?_⟩
  obtain ⟨k, hkn, x, hx, hjk, hkx, hjx⟩ := hsr.2 j hj
  exact ⟨k, hω.transitive (ZF.modelsKP hZF) n hn k hkn, x, hx, hjk,
    hkx.elim (fun p hp => ⟨p, hp.1, hsg p hp.2⟩), hjx⟩

/-- 任意实际可数约束族有统一求值；每个约束可以来自不同且任意大的有限支撑。 -/
theorem es_joint_fiber_l (hZF : M.Models ZF) {ω κ L F S P A B : M.Domain}
    (hω : M.IsOmega ω) (hωL : M.MemberSubset ω L) (hF : Em_family_d ω κ L F)
    (hco : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (complete : ∀ H f, Ef_levels_d ω κ H → Es_fiber_d (kp_pair_l (ZF.modelsKP hZF)) ω L F H f →
      ∃ g, Ef_fiber_d ω κ H g)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hA : Fn0_d ω S A) (hB : Fn0_d ω P B)
    (large : ∀ i a E U, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a U F → M.mem E U) :
    ∃ f g, M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) f ω L ∧ Fn0_d ω κ g ∧
      (∀ i a j x, Rd_entry_d i a A → Rd_entry_d j x a → ∃ n, Rd_entry_d n x f) ∧
      ∀ i a E, Rd_entry_d i a A → Rd_entry_d i E B → ∃ r, M.mem r E ∧ Ec_eval_d ω κ L f g a r := by
  obtain ⟨C, hc, spec⟩ := ec_coordinates_l hZF hω hS hA
  have cl : M.MemberSubset C L := fun x hx => by
    obtain ⟨i, a, j, hia, hjx⟩ := (spec x).mp hx
    obtain ⟨_, _, ha⟩ := (hS a).mp (hA.bound_l hia).2
    exact ha.output_mem_of_pairMember hjx
  obtain ⟨f, hf, cover⟩ := ec_cover_l hZF hω hωL cl hc
  have covered i a j x (hia : Rd_entry_d i a A) (hjx : Rd_entry_d j x a) : ∃ n, Rd_entry_d n x f :=
    cover x ((spec x).mpr ⟨i, a, j, hia, hjx⟩)
  obtain ⟨H, levels, fiber, read⟩ := ec_levels_l hZF hω hF hco hS hA hB large hf
  obtain ⟨g, hg⟩ := complete H f levels fiber
  exact ⟨f, g, hf, hg.1, covered, ec_levels_realize_l hZF hω hS hA hf covered hg read⟩

end YesMetaZFC.SetTheory.LargeCardinal
