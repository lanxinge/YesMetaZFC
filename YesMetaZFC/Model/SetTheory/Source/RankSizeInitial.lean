import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.SetTheory.CumulativeRelativeAlgebra
import YesMetaZFC.SetTheory.CumulativeFunction
import YesMetaZFC.SetTheory.Card.SmallBound
import YesMetaZFC.SetTheory.CumulativeRelativeClosure
import YesMetaZFC.SetTheory.Filter.Source
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax
import YesMetaZFC.SetTheory.CumulativeRelativeRestriction
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.SetTheory.Filter.SourceUltrafilter
import YesMetaZFC.SetTheory.InaccessibleEnumeration
import YesMetaZFC.SetTheory.Card.SmallEnumeration

/-! # 相对秩层的实际初始实例与初等传输

层级存在性只从极限 Vδ 出发，不向一般 Hχ 源强加幂集封闭。
传输全称存在句子后，目标中的新序数也有唯一传递秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem vr_sat_l (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x : M.Domain // M.mem x X}) {n} (ρ : Env (rt_model_l X hn) n) (α V : Term n) :
    Formula.satisfies ρ (v_sigma_m α V) ↔ Vr_d X (α.eval ρ).val (V.eval ρ).val := by
  have matrix (η : Env (rt_model_l X hn) (n+3)) :
      Formula.satisfies η (vc_matrix_m α.weaken.weaken.weaken V.weaken.weaken.weaken (.bound 2) (.bound 1) .newest) ↔
        Vc_d (α.weaken.weaken.weaken.eval η).val (V.weaken.weaken.weaken.eval η).val
          (η.bound 2).val (η.bound 1).val (η.bound 0).val := by
    have tr := (rt_model_delta_l hX hn (vc_matrix_delta_l α.weaken.weaken.weaken
      V.weaken.weaken.weaken (.bound 2) (.bound 1) .newest) η).trans (vc_matrix_sat_l hKP ..)
    cases α <;> cases V <;> exact tr
  simp only [v_sigma_m, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff, matrix,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨B, F, h⟩ => ⟨B.val, F.val, B.property, F.property, fun t ht => h ⟨t, ht⟩⟩,
    fun ⟨B, F, hB, hF, h⟩ => ⟨⟨B, hB⟩, ⟨F, hF⟩, fun t => h t.val t.property⟩⟩

def Sc_hierarchy_d (X : M.Domain) : Prop := ∀ α, M.mem α X → M.IsOrdinal α →
  ∃ V, M.mem V X ∧ Vr_d X α V

def sc_hierarchy_m : Formula 1 0 := .forallE (.imp (KP.ord0_m .newest)
  (.existsE (v_sigma_m (.bound 1) .newest)))

theorem sc_hierarchy_sat_l (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x : M.Domain // M.mem x X}) (ρ : Env (rt_model_l X hn) 0) :
    Formula.satisfies ρ sc_hierarchy_m ↔ Sc_hierarchy_d X := by
  have ord (η : Env (rt_model_l X hn) 1) : Formula.satisfies η (KP.ord0_m .newest) ↔ M.IsOrdinal (η.bound 0).val :=
    (rt_model_delta_l hX hn (KP.ord0_delta_l _) η).trans (KP.ord0_sat_l hKP ..)
  simp only [sc_hierarchy_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, ord, vr_sat_l hKP hX hn]
  exact ⟨fun h α hα ho => (h ⟨α, hα⟩ ho).elim fun V hV => ⟨V.val, V.property, hV⟩,
    fun h α ho => (h α.val α.property ho).elim fun V hV => ⟨⟨V, hV.1⟩, hV.2⟩⟩

theorem sc_v_hierarchy_l (hZF : M.Models ZF) {δ X : M.Domain} (hδ : M.IsLimitOrdinal δ)
    (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) : Sc_hierarchy_d X := by
  intro α hα ho
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hαδ := ZF.v_ordinal_height_l hZF hX ho hα
  obtain ⟨V, hV⟩ := ZF.v_exists_l I hZF ho
  obtain ⟨B, F, hB, hF, cert, _⟩ := vr_source_l hZF hX hδ hαδ hV
  exact ⟨V, ZF.v_mem_l I hZF hV hX hαδ, B, F, hB, hF, fun t _ => cert t⟩

theorem sc_hierarchy_iff_l (hZF : M.Models ZF) {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) : Sc_hierarchy_d X ↔ Sc_hierarchy_d Y := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨x, hx⟩ := hm.1.2.1
  obtain ⟨y, hy⟩ := hn.1.2.1
  let nx : Nonempty {a // M.mem a X} := ⟨⟨x, hx⟩⟩
  let ny : Nonempty {a // M.mem a Y} := ⟨⟨y, hy⟩⟩
  let ρ : Env (rt_model_l X nx) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
  let η : Env (rt_model_l Y ny) 0 := ⟨Fin.elim0, fun _ => ⟨y, hy⟩⟩
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I he, hn.empty_pred_l I he, hj⟩ nx ny
    sc_hierarchy_m (by simp -implicitDefEqProofs [sc_hierarchy_m, Definitional.Formula.FreeClosed]) ρ η (fun i => Fin.elim0 i)
  exact (sc_hierarchy_sat_l (ZF.modelsKP hZF) hX nx ρ).symm.trans
    (tr.trans (sc_hierarchy_sat_l (ZF.modelsKP hZF) hY ny η))

theorem Smap_d.hierarchy_l (hZF : M.Models ZF) {ω c d X R Y S j α β V W : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
    (ha : Rd_entry_d α β j) (hV : Rd_entry_d V W j) : Vr_d X α V ↔ Vr_d Y β W := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hαX := hj.1.1.input_mem_of_pairMember ha
  have hβY := hj.1.1.output_mem_of_pairMember ha
  let nx : Nonempty {a // M.mem a X} := ⟨⟨α, hαX⟩⟩
  let ny : Nonempty {a // M.mem a Y} := ⟨⟨β, hβY⟩⟩
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I he, hn.empty_pred_l I he, hj⟩ nx ny
    (v_sigma_m (d := 2) (.bound 1) .newest) (by simp -implicitDefEqProofs)
    ⟨Fin.cases ⟨V, hj.1.1.input_mem_of_pairMember hV⟩ (fun _ => ⟨α, hαX⟩), fun _ => ⟨α, hαX⟩⟩
    ⟨Fin.cases ⟨W, hj.1.1.output_mem_of_pairMember hV⟩ (fun _ => ⟨β, hβY⟩), fun _ => ⟨β, hβY⟩⟩
    (Fin.cases hV (fun _ => ha))
  exact (vr_sat_l (ZF.modelsKP hZF) hX nx ..).symm.trans (tr.trans (vr_sat_l (ZF.modelsKP hZF) hY ny ..))

end YesMetaZFC.SetTheory.Internal

/-! ## 模型内的不可数共尾性及其初等保持

只记录本步真正需要的性质：模型中的每张 ω→δ 图都在 δ 内有严格界。
原正则基数给出实际实例，整条全称句子的初等保持覆盖目标中新出现的图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_omega_bound_d (ω X δ : M.Domain) : Prop := ∀ f, M.mem f X → Fn0_d ω δ f →
  ∃ β, M.mem β δ ∧ ∀ n y, Rd_entry_d n y f → M.mem y β

def sc_omega_bound_m {n} (ω δ f : Term n) : Formula 1 n := .imp (fn0_m ω δ f)
  (Formula.existsMem δ (Formula.forallMem ω.weaken (Formula.forallMem δ.weaken.weaken
    (.imp (rd_entry0_m (.bound 1) .newest f.weaken.weaken.weaken) (.mem .newest (.bound 2))))))
derive_free_closed sc_omega_bound_m

theorem sc_omega_bound_delta_l {n} (ω δ f : Term n) : (sc_omega_bound_m ω δ f).IsDelta0 :=
  .imp (fn0_delta_l ..) (.existsMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.mem _ _)))))

theorem sc_omega_bound_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω δ f : Term n) :
    Formula.satisfies ρ (sc_omega_bound_m ω δ f) ↔ (Fn0_d (ω.eval ρ) (δ.eval ρ) (f.eval ρ) →
      ∃ β, M.mem β (δ.eval ρ) ∧ ∀ i y, Rd_entry_d i y (f.eval ρ) → M.mem y β) := by
  simp only [sc_omega_bound_m, Formula.satisfies_imp_iff, fn0_sat_l hE, Formula.satisfies_existsMem_iff,
    Formula.satisfies_forallMem_iff, rd_entry0_sat_l hE, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h hf => (h hf).imp fun β hb => ⟨hb.1, fun i y hy => hb.2 i (hf.bound_l hy).1 y (hf.bound_l hy).2 hy⟩,
    fun h hf => (h hf).imp fun β hb => ⟨hb.1, fun i _ y _ hy => hb.2 i y hy⟩⟩

theorem sc_regular_bound_l (hZF : M.Models ZF) {ω δ : M.Domain}
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP hZF)) δ) (hωδ : M.mem ω δ) (X : M.Domain) :
    Sc_omega_bound_d ω X δ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro f _ hf
  have fn := fn0_function_l (ZF.modelsKP hZF) hf
  obtain ⟨A, ha⟩ := ZF.exists_range_of_setFunction hZF I fn.1 fn.2.1
  obtain ⟨β, hβ, bound⟩ := (hr.range_bounded_of_domain_mem hZF I hωδ fn ha).exists_bound
  obtain ⟨γ, hγ, hβγ⟩ := hr.isLimitOrdinal.2.2 β hβ
  exact ⟨γ, hγ, fun i y hy => (bound y ((ha y).mpr ⟨i, hy⟩)).elim
    (fun eq => eq.symm ▸ hβγ) ((hr.isCardinal.1.mem hγ).transitive β hβγ y)⟩

theorem smap_omega_bound_l (hZF : M.Models ZF) {ω c d X R Y S j δ ε : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) (hωX : M.mem ω X) (hδε : Rd_entry_d δ ε j) :
    Sc_omega_bound_d ω X δ ↔ Sc_omega_bound_d ω Y ε := by
  have tr := hj.forall_delta_l hZF hω hX hY hm hn (n := 2) (sc_omega_bound_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (sc_omega_bound_delta_l ..)
    ⟨Fin.cases δ (fun _ => ω), fun _ => ω⟩ ⟨Fin.cases ε (fun _ => ω), fun _ => ω⟩
    (Fin.cases hδε (fun _ => hj.omega_l _ hZF hω hX hY hm hn hωX))
  simpa only [sc_omega_bound_sat_l hZF.1] using! tr

/-- 模型内正则性所需的全部较小序数域；不要求背景中的正则性。 -/
def Sc_regular_d (X δ : M.Domain) : Prop := ∀ μ, M.mem μ δ → Sc_omega_bound_d μ X δ

theorem sc_regular_l (hZF : M.Models ZF) {δ : M.Domain}
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP hZF)) δ) (X : M.Domain) : Sc_regular_d X δ :=
  fun _ hμ => sc_regular_bound_l hZF hr hμ X

theorem Smap_d.regular_l (hZF : M.Models ZF) {ω c d X R Y S j δ ε : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) (hδε : Rd_entry_d δ ε j) :
    Sc_regular_d X δ ↔ Sc_regular_d Y ε := by
  have tr := hj.forall_delta_l hZF hω hX hY hm hn (n := 1)
    (Formula.forallMem (.bound 1) (sc_omega_bound_m .newest (.bound 2) (.bound 1)))
    (by simp -implicitDefEqProofs) (.forallMem _ (sc_omega_bound_delta_l ..))
    ⟨fun _ => δ, fun _ => δ⟩ ⟨fun _ => ε, fun _ => ε⟩ (fun _ => hδε)
  simp only [Formula.satisfies_forallMem_iff, sc_omega_bound_sat_l hZF.1] at tr
  change (∀ f, M.mem f X → ∀ μ, M.mem μ δ → _) ↔ (∀ f, M.mem f Y → ∀ μ, M.mem μ ε → _) at tr
  exact ⟨fun h μ hμ f hf => tr.mp (fun f hf μ hμ => h μ hμ f hf) f hf μ hμ,
    fun h μ hμ f hf => tr.mpr (fun f hf μ hμ => h μ hμ f hf) f hf μ hμ⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 秩模型的相对幂集闭包

幂集仅包含当前源已有的子集。极限 Vδ 给出实际初始实例；
闭包沿全初等图双向传输，并在严格相对极限秩段中保持。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}}

def Sc_power_d (X : M.Domain) : Prop := ∀ A, M.mem A X → ∃ P, M.mem P X ∧ Source_d X A P

/-- 给定相对幂集的实际像收集目标中全部已有子集。 -/
theorem Smap_d.power_l (hZF : M.Models ZF) {ω c d X R Y S j A A' P P' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
    (hA : Rd_entry_d A A' j) (hP : Rd_entry_d P P' j) (power : Source_d X A P) : Source_d Y A' P' := by
  let φ : Formula 1 3 := .iff (.mem .newest (.bound 1)) (Formula.subset .newest (.bound 2))
  have tr := hj.forall_delta_l hZF hω hX hY hm hn φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) (.iff (.mem ..) (.atom ..))
    ⟨Fin.cases P (fun _ => A), fun _ => A⟩ ⟨Fin.cases P' (fun _ => A'), fun _ => A'⟩ (Fin.cases hP (fun _ => hA))
  simp only [φ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff] at tr
  have read := tr.mp (fun x hx => (power x).trans ⟨And.right, fun hs => ⟨hx, hs⟩⟩)
  exact fun x => ⟨fun hx => ⟨hY P' (hj.1.1.output_mem_of_pairMember hP) x hx,
    (read x (hY P' (hj.1.1.output_mem_of_pairMember hP) x hx)).mp hx⟩, fun ⟨hx, hs⟩ => (read x hx).mpr hs⟩

theorem sc_power_subset_l (hZF : M.Models ZF) {ω c X R A B P : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R)
    (hB : M.mem B X) (hP : M.mem P X) (power : Source_d X A P) (sub : M.MemberSubset B A) :
    ∃ Q, M.mem Q X ∧ Source_d X B Q := by
  let ρ : Env M 1 := ⟨fun _ => B, fun _ => B⟩
  let φ : UnarySchema 1 := { body := Formula.subset .newest (.bound 1) }
  obtain ⟨Q, hQ, spec⟩ := sc_separate_source_l _ hZF hω hX hm theory φ (.atom ..) ρ (fun _ => hB) hP
  refine ⟨Q, hQ, fun C => (spec C).trans ((and_congr_right fun _ => Formula.satisfies_subset_iff ..).trans ?_)⟩
  exact ⟨fun ⟨hc, cb⟩ => ⟨((power C).mp hc).1, cb⟩,
    fun ⟨hc, cb⟩ => ⟨(power C).mpr ⟨hc, fun x hx => sub x (cb x hx)⟩, cb⟩⟩

/-- 相对幂集只收集源已有的函数；不增添外部代表元。 -/
theorem sc_function_space_l (hZF : M.Models ZF) {ω c X R D A : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R) (power : Sc_power_d X)
    (hD : M.mem D X) (hA : M.mem A X) : ∃ G, M.mem G X ∧ ∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D A f := by
  obtain ⟨P, hP, product⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX hm).product D A hD hA
  obtain ⟨B, hB, subsets⟩ := power P hP
  let ρ : Env M 2 := ⟨Fin.cases A (fun _ => D), fun _ => D⟩
  let φ : UnarySchema 2 := { body := fn0_m (.bound 2) (.bound 1) .newest }
  obtain ⟨G, hG, spec⟩ := sc_separate_source_l _ hZF hω hX hm theory φ (fn0_delta_l ..)
    ρ (Fin.cases hA (fun _ => hD)) hB
  refine ⟨G, hG, fun f => (spec f).trans ((and_congr_right fun _ => fn0_sat_l hZF.1 ..).trans ?_)⟩
  exact ⟨fun ⟨hf, fn⟩ => ⟨((subsets f).mp hf).1, fn⟩,
    fun ⟨hf, fn⟩ => ⟨(subsets f).mpr ⟨hf, fun p hp => (product p).mpr (fn.1 p hp)⟩, fn⟩⟩

def sc_power_m : Formula 1 0 := .forallE (.existsE (Formula.isPowerSet .newest (.bound 1)))
derive_free_closed sc_power_m

theorem sc_power_sat_l {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x // M.mem x X}) (ρ : Env (rt_model_l X hn) 0) :
    Formula.satisfies ρ sc_power_m ↔ Sc_power_d X := by
  have sub {d} (η : Env (rt_model_l X hn) d) (a b : Term d) : Formula.satisfies η (Formula.subset a b) ↔
      M.MemberSubset (a.eval η).val (b.eval η).val := by
    simpa only [Formula.subset, Structure.MemberSubset, eval_image_env_l (M := rt_model_l X hn) (N := M) Subtype.val] using
      (rt_model_delta_l hX hn (.atom ..) η).trans (Formula.satisfies_subset_iff _ a b)
  simp only [sc_power_m, Formula.isPowerSet, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, sub]
  constructor
  · intro h A hA
    obtain ⟨P, hp⟩ := h ⟨A, hA⟩
    exact ⟨P.val, P.property, fun B => ⟨fun hB => ⟨hX P.val P.property B hB,
      (hp ⟨B, hX P.val P.property B hB⟩).mp hB⟩, fun ⟨hB, ba⟩ => (hp ⟨B, hB⟩).mpr ba⟩⟩
  · intro h A
    obtain ⟨P, hp, spec⟩ := h A.val A.property
    exact ⟨⟨P, hp⟩, fun B => (spec B.val).trans (and_iff_right B.property)⟩

theorem sc_v_power_l (hKP : M.Models KP) {δ V : M.Domain} (hδ : M.IsLimitOrdinal δ)
    (hV : V_d (kp_pair_l hKP) δ V) : Sc_power_d V := by
  intro A hA
  obtain ⟨P, hp⟩ := v_power_exists_l _ hKP hV hA
  exact ⟨P, v_power_mem_l _ hV hδ hA hp, fun B => (hp B).trans
    ⟨fun sub => ⟨v_subset_mem_l _ hV hA sub, sub⟩, And.right⟩⟩

theorem sc_power_iff_l (hZF : M.Models ZF) {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) : Sc_power_d X ↔ Sc_power_d Y := by
  obtain ⟨x, hx⟩ := hm.1.2.1
  obtain ⟨y, hy⟩ := hn.1.2.1
  let nx : Nonempty {a // M.mem a X} := ⟨⟨x, hx⟩⟩
  let ny : Nonempty {a // M.mem a Y} := ⟨⟨y, hy⟩⟩
  let ρ : Env (rt_model_l X nx) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
  let η : Env (rt_model_l Y ny) 0 := ⟨Fin.elim0, fun _ => ⟨y, hy⟩⟩
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ he, hn.empty_pred_l _ he, hj⟩ nx ny
    sc_power_m (by simp -implicitDefEqProofs [sc_power_m, Definitional.Formula.FreeClosed]) ρ η (fun i => Fin.elim0 i)
  exact (sc_power_sat_l hX nx ρ).symm.trans (tr.trans (sc_power_sat_l hY ny η))

theorem Sc_power_d.rank_l {Z α V : M.Domain} (h : Sc_power_d Z)
    (hZ : M.TransitiveSet Z) (hV : M.mem V Z) (rank : Vr_d Z α V) (hα : M.IsLimitOrdinal α) : Sc_power_d V := by
  intro A hA
  obtain ⟨P, hP, spec⟩ := h A (hZ V hV A hA)
  have hPV := rank.subsets_mem_l hZ hV hα hA hP (fun B hB => ((spec B).mp hB).2)
  exact ⟨P, hPV, fun B => ⟨fun hB => ⟨rank.transitive_l hZ hV P hPV B hB, ((spec B).mp hB).2⟩,
    fun ⟨hB, sub⟩ => (spec B).mpr ⟨hZ V hV B hB, sub⟩⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 所属模型中的原始不可达性

正则性使用原始共尾度定义，强极限性使用原始幂集基数定义。
任意包含 κ 的秩层直接回收共尾图与单射图；不要求该秩层满足 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sc_inaccessible_m {d} (ω κ : Term d) : Formula 1 d := .conj (.mem ω κ)
  (.conj (Formula.isRegularCardinal kpair_convention_l κ) (Formula.isStrongLimitCardinal kpair_convention_l κ))
derive_free_closed sc_inaccessible_m

def Sc_inaccessible_d (ω X κ : M.Domain) : Prop :=
  ∃ hω : M.mem ω X, ∃ hκ : M.mem κ X, Formula.satisfies
    (⟨Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, hω⟩), fun _ => ⟨ω, hω⟩⟩ : Env (rt_model_l X ⟨⟨ω, hω⟩⟩) 2)
    (sc_inaccessible_m (.bound 1) .newest)

theorem sc_inaccessible_sat_l (hE : Extensional M) {X : M.Domain} (hX : M.TransitiveSet X)
    (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (nx : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X nx) d) (ω κ : Term d) :
    Formula.satisfies ρ (sc_inaccessible_m ω κ) ↔ Sc_inaccessible_d (ω.eval ρ).val X (κ.eval ρ).val := by
  let J := rt_pair_l hX nx hE hp
  simp only [Sc_inaccessible_d, sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff J (rt_model_ext_l hE hX nx),
    Formula.satisfies_isStrongLimitCardinal_iff J (rt_model_ext_l hE hX nx)]
  exact ⟨fun h => ⟨(ω.eval ρ).property, (κ.eval ρ).property, h⟩, fun ⟨_, _, h⟩ => h⟩

/-- 内部正则性的实际共尾见证保证该序数在背景中也是极限序数。 -/
theorem Sc_inaccessible_d.limit_l (hKP : M.Models KP) {ω X κ : M.Domain} (hX : M.TransitiveSet X)
    (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (h : Sc_inaccessible_d ω X κ) : M.IsLimitOrdinal κ := by
  obtain ⟨hω, hκ, h⟩ := h
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hω⟩⟩
  let J := rt_pair_l hX nx hKP.1 hp
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff J (rt_model_ext_l hKP.1 hX nx)] at h
  exact (rt_limit_l hX nx hKP ⟨κ, hκ⟩).mp h.2.1.isLimitOrdinal

/-- 完整初等图传输原始公式，不把目标内部不可达性提升为背景不可达性。 -/
theorem Sc_inaccessible_d.map_l (hZF : M.Models ZF) {ω c d X R Y S j κ κ' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) (hκ : Rd_entry_d κ κ' j)
    (h : Sc_inaccessible_d ω X κ) : Sc_inaccessible_d ω Y κ' := by
  obtain ⟨hωX, hκX, h⟩ := h
  have hωj := hj.omega_l _ hZF hω hX hY hm hn hωX
  have hωY := hj.1.1.output_mem_of_pairMember hωj
  have hκY := hj.1.1.output_mem_of_pairMember hκ
  let ρ : Env (rt_model_l X ⟨⟨ω, hωX⟩⟩) 2 :=
    ⟨Fin.cases ⟨κ, hκX⟩ (fun _ => ⟨ω, hωX⟩), fun _ => ⟨ω, hωX⟩⟩
  let η : Env (rt_model_l Y ⟨⟨ω, hωY⟩⟩) 2 :=
    ⟨Fin.cases ⟨κ', hκY⟩ (fun _ => ⟨ω, hωY⟩), fun _ => ⟨ω, hωY⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  exact ⟨hωY, hκY, (spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ hz, hn.empty_pred_l _ hz, hj⟩
    ⟨⟨ω, hωX⟩⟩ ⟨⟨ω, hωY⟩⟩ (sc_inaccessible_m (.bound 1) .newest) (by simp -implicitDefEqProofs)
    ρ η (Fin.cases hκ (fun _ => hωj))).mp h⟩

/-- 极限 Vκ 中的坐标编码仍在 Vκ，故整个函数图属于任意包含 κ 的秩层。 -/
theorem sc_rank_graph_l (hZF : M.Models ZF) {δ X κ K A B f : M.Domain}
    (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hκ : M.mem κ X)
    (limit : M.IsLimitOrdinal κ) (hK : V_d (kp_pair_l (ZF.modelsKP hZF)) κ K)
    (hA : M.MemberSubset A K) (hB : M.MemberSubset B K)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f A B) : M.mem f X := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hKX := ZF.v_mem_l I hZF hK hX (ZF.v_ordinal_height_l hZF hX limit.1 hκ)
  have pair := sc_v_pair_l (ZF.modelsKP hZF) limit hK
  apply v_subset_mem_l I hX hKX
  intro p hp
  obtain ⟨a, b, code⟩ := hf.1.1 p hp
  have ha := hA a (hf.input_mem_of_pairMember ⟨p, code, hp⟩)
  have hb := hB b (hf.output_mem_of_pairMember ⟨p, code, hp⟩)
  obtain ⟨s, hs, ps⟩ := pair a a ha ha
  obtain ⟨t, ht, pt⟩ := pair a b ha hb
  obtain ⟨q, hq, pq⟩ := pair s t hs ht
  have cp : KPair_d M q a b := ⟨s, t, fun z => (ps z).trans ⟨fun h => h.elim id id, Or.inl⟩, pt, pq⟩
  exact kpair_unique_l M hZF.1 cp code ▸ hq
/-- 任意包含 κ 的秩层都正确读取其不可达性；无需层高为极限。
    图中每个有序对属于 Vκ，故整张图属于外层。 -/
theorem sc_v_inaccessible_l (hZF : M.Models ZF) {δ X ω κ : M.Domain}
    (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hκ : M.mem κ X) (above : M.mem ω κ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP hZF)) κ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP hZF)) κ) : Sc_inaccessible_d ω X κ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := v_transitive_l I hX
  have hω := ht κ hκ ω above
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hω⟩⟩
  let N := rt_model_l X nx
  let ρ : Env N 2 := ⟨Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, hω⟩), fun _ => ⟨ω, hω⟩⟩
  obtain ⟨K, hK⟩ := ZF.v_exists_l I hZF hr.1.1
  have kt := v_transitive_l I hK
  have graph {A B f} := @sc_rank_graph_l M hZF δ X κ K A B f hX hκ hr.isLimitOrdinal hK
  have cardinal := rt_cardinal_formula_l (ZF.modelsKP hZF) ht nx ρ (.bound 0) hr.1
  refine ⟨hω, hκ, ?_⟩
  change Formula.satisfies ρ (sc_inaccessible_m (.bound 1) .newest)
  simp only [sc_inaccessible_m, Formula.isRegularCardinal, Formula.isCofinality,
    Formula.isStrongLimitCardinal, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.hasCofinalOrdinalSequence, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hZF.1 ht nx),
    rt_cofinal_formula_l (ZF.modelsKP hZF) ht nx, Formula.satisfies_forallMem_iff,
    Formula.satisfies_isPowerSet_iff, Formula.cardinalLess, Formula.cardinalLessOrEqual,
    Formula.equinumerous, Formula.satisfies_neg_iff,
    rt_injection_formula_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)),
    rt_bijection_formula_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)),
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_zero_push,
    Term.eval_bound_one_push]
  refine ⟨above, ⟨cardinal, ?_, ?_⟩, cardinal, ?_⟩
  · obtain ⟨f, cf⟩ := hr.2.1
    have hf := graph (ZF.v_ordinal_subset_l I hZF hK) (ZF.v_ordinal_subset_l I hZF hK) cf.isSetFunctionFromTo
    obtain ⟨R, range, _⟩ := cf.2.2.1.2.2
    exact ⟨⟨f, hf⟩, cf, R, v_subset_mem_l I hX hκ (cf.range_isCofinalSubset hZF.1 range).2.1, range⟩
  · rintro μ ⟨f, hf, _⟩
    exact (hr.2.2 μ.val ⟨f.val, hf⟩).imp Subtype.ext id
  · intro a ha P power
    have pow : M.IsPowerSetOf P.val a.val := by
      intro B
      refine ⟨fun hb x hx => ?_, fun sub => ?_⟩
      · exact (power ⟨B, ht P.val P.property B hb⟩).mp hb ⟨x, ht B (ht P.val P.property B hb) x hx⟩ hx
      · exact (power ⟨B, v_subset_mem_l I hX a.property sub⟩).mpr (fun x hx => sub x.val hx)
    have hPK := v_power_mem_l I hK hr.isLimitOrdinal (ZF.v_ordinal_mem_l I hZF hK ha) pow
    obtain ⟨⟨f, hf⟩, not_bij⟩ := hs.2 a.val ha P.val pow
    exact ⟨⟨⟨f, graph (kt P.val hPK) (ZF.v_ordinal_subset_l I hZF hK) hf.1⟩, hf⟩,
      fun ⟨g, hg⟩ => not_bij ⟨g.val, hg⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原始不可达性在严格极限秩段中的保持

共尾序列及其值域、幂集上的单射都由原源提供，再由实际秩闭包回收。
秩段的相对幂集包含原源已有的全部子集；不假定外部子集也在原源中。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem Sc_inaccessible_d.rank_l (hZF : M.Models ZF) {ω X α V κ : M.Domain}
    (hX : M.TransitiveSet X) (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (hV : M.mem V X) (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α) (hκ : M.mem κ V)
    (h : Sc_inaccessible_d ω X κ) : Sc_inaccessible_d ω V κ := by
  obtain ⟨hωX, hκX, h⟩ := h
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hωX⟩⟩
  let N := rt_model_l X nx
  let J := rt_pair_l hX nx hZF.1 hp
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff J (rt_model_ext_l hZF.1 hX nx),
    Formula.satisfies_isStrongLimitCardinal_iff J (rt_model_ext_l hZF.1 hX nx)] at h
  change M.mem ω κ ∧ N.IsRegularCardinal J ⟨κ, hκX⟩ ∧ N.IsStrongLimitCardinal J ⟨κ, hκX⟩ at h
  obtain ⟨above, hr, hs⟩ := h
  have ht := rank.transitive_l hX hV
  have hωV := ht κ hκ ω above
  let nv : Nonempty {x // M.mem x V} := ⟨⟨ω, hωV⟩⟩
  let Q := rt_model_l V nv
  have pq : ∀ a b, M.mem a V → M.mem b V → ∃ p, M.mem p V ∧ Pair_d M p a b := by
    intro a b ha hb
    obtain ⟨p, hpx, pair⟩ := hp a b (hX V hV a ha) (hX V hV b hb)
    exact ⟨p, rank.pair_mem_l hZF hX hV hα ha hb hpx pair, pair⟩
  let K := rt_pair_l ht nv hZF.1 pq
  let l (x : Q.Domain) : N.Domain := ⟨x.val, hX V hV x.val x.property⟩
  let k : Q.Domain := ⟨κ, hκ⟩
  have cardinal := rt_cardinal_restrict_l hX nx hZF.1 hp
    (ZF.modelsKP hZF) ht nv pq (hX V hV) k hr.1
  refine ⟨hωV, hκ, ?_⟩
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff K (rt_model_ext_l hZF.1 ht nv),
    Formula.satisfies_isStrongLimitCardinal_iff K (rt_model_ext_l hZF.1 ht nv)]
  change M.mem ω κ ∧ Q.IsRegularCardinal K k ∧ Q.IsStrongLimitCardinal K k
  refine ⟨above, ⟨cardinal, ?_, ?_⟩, cardinal, ?_⟩
  -- 保留原共尾图及其实际值域；较短共尾序列反向读入原源，违反原正则性。
  · obtain ⟨f, cofinal⟩ := hr.2.1
    have cf := rt_cofinal_up_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp (ZF.modelsKP hZF) f (l k) (l k) cofinal
    have ff := cf.isSetFunctionFromTo
    have hf := rank.relation_mem_l hX hV hα hκ hκ f.property (fun p hpf => by
      obtain ⟨a, b, pair⟩ := ff.1.1 p hpf
      exact ⟨a, ff.input_mem_of_pairMember ⟨p, pair, hpf⟩, b, ff.output_mem_of_pairMember ⟨p, pair, hpf⟩, pair⟩)
    obtain ⟨R, range, _⟩ := cofinal.2.2.1.2.2
    have range := (rt_range_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp R f).mp range
    have hR := rank.subset_mem_l hX hV hκ R.property (cf.range_isCofinalSubset hZF.1 range).2.1
    exact ⟨⟨f.val, hf⟩, rt_cofinal_down_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq
      ⟨f.val, hf⟩ k k ⟨R.val, hR⟩ range cf⟩
  · rintro μ ⟨f, cofinal⟩
    have cf := rt_cofinal_up_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq (ZF.modelsKP hZF) f μ k cofinal
    obtain ⟨R, range, _⟩ := cofinal.2.2.1.2.2
    have range := (rt_range_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq R f).mp range
    rcases hr.2.2 (l μ) ⟨l f, rt_cofinal_down_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp
      (l f) (l μ) (l k) (l R) range cf⟩ with eq | lt
    · exact Or.inl (Subtype.ext (congrArg (fun x : N.Domain => x.val) eq))
    · exact Or.inr lt
  -- 截断包含原源已有的每个小子集，所以两源的相对幂集相同。
  · intro a ha P power
    have pow : N.IsPowerSetOf (l P) (l a) := by
      intro B
      refine ⟨fun hb z hz => ?_, fun sub => ?_⟩
      · have hB := ht P.val P.property B.val hb
        exact (power ⟨B.val, hB⟩).mp hb ⟨z.val, ht B.val hB z.val hz⟩ hz
      · have sub' : M.MemberSubset B.val a.val := fun z hz => sub ⟨z, hX B.val B.property z hz⟩ hz
        have hB := rank.subset_mem_l hX hV a.property B.property sub'
        exact (power ⟨B.val, hB⟩).mpr (fun z hz => sub (l z) hz)
    obtain ⟨⟨f, ff⟩, not_bij⟩ := hs.2 (l a) ha (l P) pow
    have ff := (rt_injection_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp f (l P) (l k)).mp ff
    have hf := rank.relation_mem_l hX hV hα P.property hκ f.property (fun p hpf => by
      obtain ⟨a, b, pair⟩ := ff.1.1.1 p hpf
      exact ⟨a, ff.1.input_mem_of_pairMember ⟨p, pair, hpf⟩, b, ff.1.output_mem_of_pairMember ⟨p, pair, hpf⟩, pair⟩)
    refine ⟨⟨⟨f.val, hf⟩, (rt_injection_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq ⟨f.val, hf⟩ P k).mpr ff⟩, ?_⟩
    rintro ⟨g, gg⟩
    exact not_bij ⟨l g, (rt_bijection_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp (l g) (l P) (l k)).mpr
      ((rt_bijection_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq g P k).mp gg)⟩

/-- 截断也包含原源中所有相关图和小幂集，故原不可达性判断反向保持。 -/
theorem Sc_inaccessible_d.of_rank_l (hZF : M.Models ZF) {ω X α V κ : M.Domain}
    (hX : M.TransitiveSet X) (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (hV : M.mem V X) (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α)
    (h : Sc_inaccessible_d ω V κ) : Sc_inaccessible_d ω X κ := by
  obtain ⟨hω, hκ, h⟩ := h
  have ht := rank.transitive_l hX hV
  have hωX := hX V hV ω hω
  have hκX := hX V hV κ hκ
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hωX⟩⟩
  let nv : Nonempty {x // M.mem x V} := ⟨⟨ω, hω⟩⟩
  let N := rt_model_l X nx
  let Q := rt_model_l V nv
  have pq : ∀ a b, M.mem a V → M.mem b V → ∃ p, M.mem p V ∧ Pair_d M p a b := by
    intro a b ha hb
    obtain ⟨p, hpx, pair⟩ := hp a b (hX V hV a ha) (hX V hV b hb)
    exact ⟨p, rank.pair_mem_l hZF hX hV hα ha hb hpx pair, pair⟩
  let I := rt_pair_l hX nx hZF.1 hp
  let J := rt_pair_l ht nv hZF.1 pq
  let l (x : Q.Domain) : N.Domain := ⟨x.val, hX V hV x.val x.property⟩
  let k : Q.Domain := ⟨κ, hκ⟩
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff J (rt_model_ext_l hZF.1 ht nv),
    Formula.satisfies_isStrongLimitCardinal_iff J (rt_model_ext_l hZF.1 ht nv)] at h
  change M.mem ω κ ∧ Q.IsRegularCardinal J k ∧ Q.IsStrongLimitCardinal J k at h
  obtain ⟨above, hr, hs⟩ := h
  have ho := (rt_ordinal_iff_l ht nv (ZF.modelsKP hZF) k).mp hr.1.1
  have cardinal : N.IsCardinal I (l k) := by
    refine ⟨rt_ordinal_l hX nx (l k) ho, ?_⟩
    rintro μ hμ ⟨f, bf⟩
    have bf := (rt_bijection_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp f μ (l k)).mp bf
    have hμV := ht κ hκ μ.val hμ
    have hf := rank.relation_mem_l hX hV hα hμV hκ f.property (fn0_of_function_l (ZF.modelsKP hZF) bf.1.1).1
    exact hr.1.2 ⟨μ.val, hμV⟩ hμ ⟨⟨f.val, hf⟩,
      (rt_bijection_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq ⟨f.val, hf⟩ ⟨μ.val, hμV⟩ k).mpr bf⟩
  refine ⟨hωX, hκX, ?_⟩
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff I (rt_model_ext_l hZF.1 hX nx),
    Formula.satisfies_isStrongLimitCardinal_iff I (rt_model_ext_l hZF.1 hX nx)]
  change M.mem ω κ ∧ N.IsRegularCardinal I (l k) ∧ N.IsStrongLimitCardinal I (l k)
  refine ⟨above, ⟨cardinal, ?_, ?_⟩, cardinal, ?_⟩
  · obtain ⟨f, cf⟩ := hr.2.1
    obtain ⟨R, range, _⟩ := cf.2.2.1.2.2
    exact ⟨l f, rt_cofinal_down_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp (l f) (l k) (l k) (l R)
      ((rt_range_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq R f).mp range)
      (rt_cofinal_up_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq (ZF.modelsKP hZF) f k k cf)⟩
  · rintro μ ⟨f, cf⟩
    have cf' := rt_cofinal_up_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp (ZF.modelsKP hZF) f μ (l k) cf
    rcases ho.trichotomy hZF.1 cf'.2.1.1.1.1 (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) κ μ.val) with eq | lt | gt
    · exact Or.inl (Subtype.ext (hZF.1.eq_of_same_members κ μ.val eq))
    · exact Or.inr lt
    · have hμV := ht κ hκ μ.val gt
      have hf := rank.relation_mem_l hX hV hα hμV hκ f.property
        (fn0_of_function_l (ZF.modelsKP hZF) cf'.isSetFunctionFromTo).1
      obtain ⟨R, range, _⟩ := cf.2.2.1.2.2
      have range := (rt_range_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp R f).mp range
      have hR := rank.subset_mem_l hX hV hκ R.property (cf'.range_isCofinalSubset hZF.1 range).2.1
      exact (hr.2.2 ⟨μ.val, hμV⟩ ⟨⟨f.val, hf⟩, rt_cofinal_down_l ht nv hZF.1
        (KP.exists_pair (ZF.modelsKP hZF)) pq ⟨f.val, hf⟩ ⟨μ.val, hμV⟩ k ⟨R.val, hR⟩ range cf'⟩).imp
        (fun eq => Subtype.ext (congrArg (fun x : Q.Domain => x.val) eq)) id
  · intro a ha P power
    have haV := ht κ hκ a.val ha
    have bound : ∀ B, M.mem B P.val → M.MemberSubset B a.val := fun B hb z hz =>
      (power ⟨B, hX P.val P.property B hb⟩).mp hb ⟨z, hX B (hX P.val P.property B hb) z hz⟩ hz
    have hPV := rank.subsets_mem_l hX hV hα haV P.property bound
    have pow : Q.IsPowerSetOf ⟨P.val, hPV⟩ ⟨a.val, haV⟩ := fun B =>
      ⟨fun hb z hz => (power (l B)).mp hb (l z) hz,
        fun sub => (power (l B)).mpr (fun z hz => sub ⟨z.val, ht B.val B.property z.val hz⟩ hz)⟩
    obtain ⟨⟨f, inj⟩, not_bij⟩ := hs.2 ⟨a.val, haV⟩ ha ⟨P.val, hPV⟩ pow
    refine ⟨⟨l f, (rt_injection_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp (l f) P (l k)).mpr
      ((rt_injection_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq f ⟨P.val, hPV⟩ k).mp inj)⟩, ?_⟩
    rintro ⟨g, bg⟩
    have bg := (rt_bijection_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp g P (l k)).mp bg
    have hg := rank.relation_mem_l hX hV hα hPV hκ g.property (fn0_of_function_l (ZF.modelsKP hZF) bg.1.1).1
    exact not_bij ⟨⟨g.val, hg⟩, (rt_bijection_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq ⟨g.val, hg⟩ ⟨P.val, hPV⟩ k).mpr bg⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 任意秩层的原不可达性判断向上读取

反例图的坐标均在 Vκ 中，因而图本身已经属于当前秩层。这个精确秩界
使后继秩层也能检验全部较短双射、共尾序列及小幂集上的单射。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_v_inaccessible_read_l {η Y ω κ : M.Domain} (hY : V_d I η Y)
    (h : Sc_inaccessible_d ω Y κ) :
    M.mem ω κ ∧ M.IsRegularCardinal I κ ∧ M.IsStrongLimitCardinal I κ := by
  obtain ⟨hw, hk, h⟩ := h
  have ht := v_transitive_l I hY
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω, hw⟩⟩
  let N := rt_model_l Y ny
  simp only [sc_inaccessible_m, Formula.isRegularCardinal, Formula.isCofinality,
    Formula.isStrongLimitCardinal, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.hasCofinalOrdinalSequence, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hZF.1 ht ny),
    rt_cofinal_formula_l (ZF.modelsKP hZF) ht ny, Formula.satisfies_forallMem_iff,
    Formula.satisfies_isPowerSet_iff, Formula.cardinalLess, Formula.cardinalLessOrEqual,
    Formula.equinumerous, Formula.satisfies_neg_iff,
    rt_injection_formula_l ht ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF)),
    rt_bijection_formula_l ht ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF)),
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_zero_push,
    Term.eval_bound_one_push] at h
  obtain ⟨above, ⟨card, ⟨f, cf, _⟩, least⟩, _, small⟩ := h
  obtain ⟨K, hK⟩ := ZF.v_exists_l I hZF cf.1.1
  have ks := ZF.v_ordinal_subset_l I hZF hK
  have graph {A B g} := @sc_rank_graph_l M hZF η Y κ K A B g hY hk cf.1 hK
  have cardinal : M.IsCardinal I κ := by
    simp only [Formula.isCardinal, Formula.equinumerous, Formula.satisfies_conj_iff,
      Formula.satisfies_isOrdinal_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_exists_iff, rt_bijection_formula_l ht ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF)),
      Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at card
    refine ⟨cf.1.1, fun a ha ⟨g, hg⟩ => ?_⟩
    exact card.2 ⟨a, ht κ hk a ha⟩ ha ⟨⟨g, graph (fun x hx => ks x (cf.1.1.transitive a ha x hx)) ks hg.1.1⟩, hg⟩
  refine ⟨above, ⟨cardinal, ⟨f.val, cf⟩, ?_⟩, cardinal, ?_⟩
  · rintro μ ⟨g, hg⟩
    rcases Structure.IsOrdinal.trichotomy hZF.1 cf.1.1 hg.2.1.1.1.1
        (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) κ μ) with eq | lt | gt
    · exact Or.inl (hZF.1.eq_of_same_members κ μ eq)
    · exact Or.inr lt
    · have hm := ht κ hk μ gt
      have hgy := graph (fun x hx => ks x (cf.1.1.transitive μ gt x hx)) ks hg.isSetFunctionFromTo
      obtain ⟨R, range, _⟩ := hg.2.2.1.2.2
      have hr := v_subset_mem_l I hY hk (hg.range_isCofinalSubset hZF.1 range).2.1
      exact (least ⟨μ, hm⟩ ⟨⟨g, hgy⟩, hg, R, hr, range⟩).imp (congrArg Subtype.val) id
  · intro a ha P power
    have hay := ht κ hk a ha
    have hpk := v_power_mem_l I hK cf.1 (ZF.v_ordinal_mem_l I hZF hK ha) power
    have hp := v_transitive_l I hY K
      (ZF.v_mem_l I hZF hK hY (ZF.v_ordinal_height_l hZF hY cf.1.1 hk)) P hpk
    have pow : N.IsPowerSetOf ⟨P, hp⟩ ⟨a, hay⟩ := fun B => (power B.val).trans
      ⟨fun sub x hx => sub x.val hx, fun sub x hx => sub ⟨x, ht B.val B.property x hx⟩ hx⟩
    obtain ⟨⟨g, hg⟩, not_bij⟩ := small ⟨a, hay⟩ ha ⟨P, hp⟩ pow
    refine ⟨⟨g.val, hg⟩, fun ⟨b, hb⟩ => ?_⟩
    exact not_bij ⟨⟨b, graph (v_transitive_l I hK P hpk) ks hb.1.1⟩, hb⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 初始秩模型的不可达性向上读取

在实际极限 Vδ 中，相关函数图、值域和幂集都由秩界回收。因此内部的
基数、正则性和强极限判断就是原背景判断；一般传递源不作这一提升。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem sc_v_inaccessible_up_l (hKP : M.Models KP) {δ X ω κ : M.Domain}
    (hδ : M.IsLimitOrdinal δ) (hX : V_d (kp_pair_l hKP) δ X)
    (h : Sc_inaccessible_d ω X κ) : M.mem ω κ ∧
      M.IsRegularCardinal (kp_pair_l hKP) κ ∧
      M.IsStrongLimitCardinal (kp_pair_l hKP) κ := by
  let I := kp_pair_l hKP
  obtain ⟨hω, hκ, h⟩ := h
  have ht := v_transitive_l I hX
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hω⟩⟩
  let N := rt_model_l X nx
  have hp := sc_v_pair_l hKP hδ hX
  let J := rt_pair_l ht nx hKP.1 hp
  let k : N.Domain := ⟨κ, hκ⟩
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff J (rt_model_ext_l hKP.1 ht nx),
    Formula.satisfies_isStrongLimitCardinal_iff J (rt_model_ext_l hKP.1 ht nx)] at h
  change M.mem ω κ ∧ N.IsRegularCardinal J k ∧ N.IsStrongLimitCardinal J k at h
  obtain ⟨above, hr, hs⟩ := h
  have owned {A B f} (ha : M.mem A X) (hb : M.mem B X) (fn : Fn0_d A B f) : M.mem f X := by
    obtain ⟨U, hu, au, bu⟩ := v_joint_bound_l I hX ha hb
    exact v_relation_mem_l I hX hδ hu (fun p hp => (fn.1 p hp).elim fun a ha =>
      ha.2.elim fun b hb => ⟨a, au a ha.1, b, bu b hb.1, hb.2⟩)
  have ho := (rt_ordinal_iff_l ht nx hKP k).mp hr.1.1
  have cardinal : M.IsCardinal I κ := by
    refine ⟨ho, ?_⟩
    rintro μ hμ ⟨f, bij⟩
    have hμX := ht κ hκ μ hμ
    have hf := owned hμX hκ (fn0_of_function_l hKP bij.1.1)
    exact hr.1.2 ⟨μ, hμX⟩ hμ ⟨⟨f, hf⟩,
      (rt_bijection_l ht nx hKP.1 (KP.exists_pair hKP) hp ⟨f, hf⟩ ⟨μ, hμX⟩ k).mpr bij⟩
  refine ⟨above, ⟨cardinal, ?_, ?_⟩, cardinal, ?_⟩
  · obtain ⟨f, cf⟩ := hr.2.1
    exact ⟨f.val, rt_cofinal_up_l ht nx hKP.1 (KP.exists_pair hKP) hp hKP f k k cf⟩
  · rintro μ ⟨f, cf⟩
    rcases ho.trichotomy hKP.1 cf.2.1.1.1.1 (KP.difference_exists_d hKP)
      (KP.intersection_exists_d hKP κ μ) with eq | lt | gt
    · exact Or.inl (hKP.1.eq_of_same_members κ μ eq)
    · exact Or.inr lt
    · have hμX := ht κ hκ μ gt
      have hf := owned hμX hκ (fn0_of_function_l hKP cf.isSetFunctionFromTo)
      obtain ⟨R, range, _⟩ := cf.2.2.1.2.2
      have hR := v_subset_mem_l I hX hκ (cf.range_isCofinalSubset hKP.1 range).2.1
      exact (hr.2.2 ⟨μ, hμX⟩ ⟨⟨f, hf⟩, rt_cofinal_down_l ht nx hKP.1
        (KP.exists_pair hKP) hp ⟨f, hf⟩ ⟨μ, hμX⟩ k ⟨R, hR⟩ range cf⟩).imp
        (congrArg Subtype.val) id
  · intro a ha P power
    have haX := ht κ hκ a ha
    have hP := v_power_mem_l I hX hδ haX power
    have pow : N.IsPowerSetOf ⟨P, hP⟩ ⟨a, haX⟩ := fun B =>
      ⟨fun hb z hz => (power B.val).mp hb z.val hz,
        fun sub => (power B.val).mpr (fun z hz => sub ⟨z, ht B.val B.property z hz⟩ hz)⟩
    obtain ⟨⟨f, inj⟩, not_bij⟩ := hs.2 ⟨a, haX⟩ ha ⟨P, hP⟩ pow
    refine ⟨⟨f.val, (rt_injection_l ht nx hKP.1 (KP.exists_pair hKP) hp f ⟨P, hP⟩ k).mp inj⟩, ?_⟩
    rintro ⟨g, bij⟩
    have hg := owned hP hκ (fn0_of_function_l hKP bij.1.1)
    exact not_bij ⟨⟨g, hg⟩, (rt_bijection_l ht nx hKP.1 (KP.exists_pair hKP) hp ⟨g, hg⟩ ⟨P, hP⟩ k).mpr bij⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 不可达支撑以下的实际小秩层枚举

整层用支撑枚举，每个严格较早层用支撑以下的序数枚举。见证均属于原源，
全称存在句子的初等传输覆盖新序数；严格秩截断保留同一层和同一枚举图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure Sc_rank_size_d (I : kpair_convention_l.Interpretation M) (X L : M.Domain) : Prop where
  level : ∃ W f, M.mem W X ∧ Vr_d X L W ∧ M.mem f X ∧ M.IsSetBijectionFromTo I f L W
  lower : ∀ α, M.mem α L → ∃ W μ f,
    M.mem W X ∧ Vr_d X α W ∧ M.mem μ L ∧ M.mem f X ∧ M.IsSetBijectionFromTo I f μ W

def sc_rank_size_m {d} (L : Term d) : Formula 1 d := .conj
  (.existsE (.existsE (.conj (v_sigma_m L.weaken.weaken (.bound 1))
    (sh_bijection_m .newest L.weaken.weaken (.bound 1)))))
  (Formula.forallMem L (.existsE (Formula.existsMem L.weaken.weaken (.existsE
    (.conj (v_sigma_m (.bound 3) (.bound 2)) (sh_bijection_m .newest (.bound 1) (.bound 2)))))))
derive_free_closed sc_rank_size_m

theorem sc_rank_size_sat_l (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
    (nx : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X nx) d) (L : Term d) :
    Formula.satisfies ρ (sc_rank_size_m L) ↔ Sc_rank_size_d (kp_pair_l hKP) X (L.eval ρ).val := by
  have bij {n} (η : Env (rt_model_l X nx) n) (f A B : Term n) :
      Formula.satisfies η (sh_bijection_m f A B) ↔
        M.IsSetBijectionFromTo (kp_pair_l hKP) (f.eval η).val (A.eval η).val (B.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l X nx) (N := M) Subtype.val] using
      (rt_model_delta_l hX nx (sh_bijection_delta_l ..) η).trans (sh_bijection_sat_l hKP ..)
  simp only [sc_rank_size_m, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    vr_sat_l hKP hX nx, bij, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨⟨W, f, rank, bf⟩, lower⟩
    refine ⟨⟨W.val, f.val, W.property, rank, f.property, bf⟩, fun α hα => ?_⟩
    obtain ⟨W, μ, hμ, f, rank, bf⟩ := lower ⟨α, hX (L.eval ρ).val (L.eval ρ).property α hα⟩ hα
    exact ⟨W.val, μ.val, f.val, W.property, rank, hμ, f.property, bf⟩
  · intro h
    obtain ⟨W, f, hW, rank, hf, bf⟩ := h.level
    refine ⟨⟨⟨W, hW⟩, ⟨f, hf⟩, rank, bf⟩, fun α hα => ?_⟩
    obtain ⟨W, μ, f, hW, rank, hμ, hf, bf⟩ := h.lower α.val hα
    exact ⟨⟨W, hW⟩, ⟨μ, hX (L.eval ρ).val (L.eval ρ).property μ hμ⟩, hμ, ⟨f, hf⟩, rank, bf⟩

theorem Smap_d.rank_size_l (hZF : M.Models ZF) {ω c d X R Y S j L L' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) (hL : Rd_entry_d L L' j) :
    Sc_rank_size_d (kp_pair_l (ZF.modelsKP hZF)) X L ↔ Sc_rank_size_d (kp_pair_l (ZF.modelsKP hZF)) Y L' := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨L, hj.1.1.input_mem_of_pairMember hL⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨L', hj.1.1.output_mem_of_pairMember hL⟩⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => ⟨L, hj.1.1.input_mem_of_pairMember hL⟩, fun _ => ⟨L, hj.1.1.input_mem_of_pairMember hL⟩⟩
  let η : Env (rt_model_l Y ny) 1 := ⟨fun _ => ⟨L', hj.1.1.output_mem_of_pairMember hL⟩, fun _ => ⟨L', hj.1.1.output_mem_of_pairMember hL⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ hz, hn.empty_pred_l _ hz, hj⟩ nx ny
    (sc_rank_size_m .newest) (by simp -implicitDefEqProofs) ρ η (fun _ => hL)
  exact (sc_rank_size_sat_l (ZF.modelsKP hZF) hX nx ρ .newest).symm.trans
    (tr.trans (sc_rank_size_sat_l (ZF.modelsKP hZF) hY ny η .newest))

theorem Sc_rank_size_d.rank_l (hZF : M.Models ZF) {X α V L : M.Domain}
    (hX : M.TransitiveSet X) (hV : M.mem V X) (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α) (hL : M.mem L V)
    (h : Sc_rank_size_d (kp_pair_l (ZF.modelsKP hZF)) X L) : Sc_rank_size_d (kp_pair_l (ZF.modelsKP hZF)) V L := by
  have ht := rank.transitive_l hX hV
  have move {β μ W f} (hβ : M.mem β V) (hμ : M.mem μ V) (hW : M.mem W X) (hw : Vr_d X β W)
      (hf : M.mem f X) (bf : M.IsSetBijectionFromTo (kp_pair_l (ZF.modelsKP hZF)) f μ W) :
      M.mem W V ∧ Vr_d V β W ∧ M.mem f V := by
    obtain ⟨hW', hw'⟩ := rank.rank_l hZF hX hV hα hβ hW hw
    exact ⟨hW', hw', rank.relation_mem_l hX hV hα hμ hW' hf (fn0_of_function_l (ZF.modelsKP hZF) bf.1.1).1⟩
  obtain ⟨W, f, hW, hw, hf, bf⟩ := h.level
  obtain ⟨hW', hw', hf'⟩ := move hL hL hW hw hf bf
  refine ⟨⟨W, f, hW', hw', hf', bf⟩, fun β hβ => ?_⟩
  obtain ⟨W, μ, f, hW, hw, hμ, hf, bf⟩ := h.lower β hβ
  obtain ⟨hW', hw', hf'⟩ := move (ht L hL β hβ) (ht L hL μ hμ) hW hw hf bf
  exact ⟨W, μ, f, hW', hw', hμ, hf', bf⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 任意内部不可达支撑的正则界与秩层枚举

该原一阶句子在初始秩模型中实际成立，完整初等图可双向传输它。因此每个
后继中新出现的不可达序数也取得小秩层枚举和正则函数界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_inaccessible_closure_d (I : kpair_convention_l.Interpretation M) (ω X : M.Domain) : Prop :=
  ∀ L, Sc_inaccessible_d ω X L → Sc_regular_d X L ∧ Sc_rank_size_d I X L

def sc_inaccessible_closure_m {d} (ω : Term d) : Formula 1 d := .forallE
  (.imp (sc_inaccessible_m ω.weaken .newest) (.conj
    (Formula.forallMem .newest (.forallE (sc_omega_bound_m (.bound 1) (.bound 2) .newest)))
    (sc_rank_size_m .newest)))
derive_free_closed sc_inaccessible_closure_m

theorem sc_inaccessible_closure_sat_l (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
    (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (nx : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X nx) d) (ω : Term d) :
    Formula.satisfies ρ (sc_inaccessible_closure_m ω) ↔
      Sc_inaccessible_closure_d (kp_pair_l hKP) (ω.eval ρ).val X := by
  have bound {n} (η : Env (rt_model_l X nx) n) (μ L f : Term n) :
      Formula.satisfies η (sc_omega_bound_m μ L f) ↔ (Fn0_d (μ.eval η).val (L.eval η).val (f.eval η).val →
        ∃ β, M.mem β (L.eval η).val ∧ ∀ i y, Rd_entry_d i y (f.eval η).val → M.mem y β) := by
    simpa only [eval_image_env_l (M := rt_model_l X nx) (N := M) Subtype.val] using
      (rt_model_delta_l hX nx (sc_omega_bound_delta_l ..) η).trans (sc_omega_bound_sat_l hKP.1 ..)
  simp only [sc_inaccessible_closure_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    sc_inaccessible_sat_l hKP.1 hX hp nx, sc_rank_size_sat_l hKP hX nx, bound, Definitional.Term.eval_weaken]
  constructor
  · intro all L hL
    have copy := hL
    obtain ⟨_, hLX, _⟩ := copy
    obtain ⟨regular, sizes⟩ := all ⟨L, hLX⟩ hL
    exact ⟨fun μ hμ f hf => regular ⟨μ, hX L hLX μ hμ⟩ hμ ⟨f, hf⟩, sizes⟩
  · intro all L hL
    obtain ⟨regular, sizes⟩ := all L.val hL
    exact ⟨fun μ hμ f => regular μ.val hμ f.val f.property, sizes⟩

theorem sc_inaccessible_closure_iff_l (hZF : M.Models ZF) {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (px : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (py : ∀ a b, M.mem a Y → M.mem b Y → ∃ p, M.mem p Y ∧ Pair_d M p a b)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) (hωX : M.mem ω X) :
    Sc_inaccessible_closure_d (kp_pair_l (ZF.modelsKP hZF)) ω X ↔
      Sc_inaccessible_closure_d (kp_pair_l (ZF.modelsKP hZF)) ω Y := by
  have hw := hj.omega_l _ hZF hω hX hY hm hn hωX
  have hωY := hj.1.1.output_mem_of_pairMember hw
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hωX⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω, hωY⟩⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => ⟨ω, hωX⟩, fun _ => ⟨ω, hωX⟩⟩
  let η : Env (rt_model_l Y ny) 1 := ⟨fun _ => ⟨ω, hωY⟩, fun _ => ⟨ω, hωY⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ hz, hn.empty_pred_l _ hz, hj⟩ nx ny
    (sc_inaccessible_closure_m .newest) (by simp -implicitDefEqProofs) ρ η (fun _ => hw)
  exact (sc_inaccessible_closure_sat_l (ZF.modelsKP hZF) hX px nx ρ .newest).symm.trans
    (tr.trans (sc_inaccessible_closure_sat_l (ZF.modelsKP hZF) hY py ny η .newest))

theorem Sc_inaccessible_closure_d.rank_l (hZF : M.Models ZF) {ω X α V : M.Domain}
    (hX : M.TransitiveSet X) (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (hV : M.mem V X) (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α)
    (h : Sc_inaccessible_closure_d (kp_pair_l (ZF.modelsKP hZF)) ω X) :
    Sc_inaccessible_closure_d (kp_pair_l (ZF.modelsKP hZF)) ω V := by
  intro L inaccessible
  obtain ⟨regular, sizes⟩ := h L (inaccessible.of_rank_l hZF hX hp hV rank hα)
  obtain ⟨_, hL, _⟩ := inaccessible
  exact ⟨fun μ hμ f hf => regular μ hμ f (hX V hV f hf), sizes.rank_l hZF hX hV rank hα hL⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原秩历史的实际前缀与极限层展开

在所属源中限制原历史函数，得到同一较早层的相对秩证书。极限层中的每个
对象随后进入某个严格较早层；没有另选背景中的完整幂集层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_rank_stage_l {ω c X R α V B F β W : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hV : M.mem V X) (hB : M.mem B X) (hF : M.mem F X)
    (cert : ∀ t, M.mem t X → Vc_d α V B F t) (hβ : M.mem β α) (hW : Rd_entry_d β W F) : Vr_d X β W := by
  have ho := (cert V hV).1
  have fn := (cert V hV).2.1
  have hβX := (rd_entry_transitive_l hX hF hW).1
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 1 := { body := rd_entry0_m (.bound 1) .newest (.bound 2) }
  have sat a b : φ.denote ρ a b ↔ Rd_entry_d a b F := rd_entry0_sat_l hZF.1 ..
  obtain ⟨G, hG, gf, select⟩ := sc_uniform_source_l hZF hω hX hm theory φ (rd_entry0_delta_l ..)
    ρ (fun _ => hF) hβX hB (fun a ha => (fn.2.1 a (ho.transitive β hβ a ha)).imp fun b hb => ⟨hb.1, (sat a b).mpr hb.2⟩)
  have edge a (ha : M.mem a β) b : Rd_entry_d a b G ↔ Rd_entry_d a b F := by
    refine ⟨fun h => (sat a b).mp (select a b h), fun h => ?_⟩
    obtain ⟨v, _, hav⟩ := gf.2.1 a ha
    exact (fn0_function_l (ZF.modelsKP hZF) fn).1.2 a v b ((sat a v).mp (select a v hav)) h ▸ hav
  have step δ (sub : M.MemberSubset δ β) U t : Vc_step_d δ B F U t ↔ Vc_step_d δ B G U t :=
    iff_congr Iff.rfl (exists_congr fun γ => and_congr_right fun hγ => exists_congr fun T =>
      and_congr_right fun _ => and_congr (edge γ (sub γ hγ) T).symm Iff.rfl)
  refine ⟨B, G, hB, hG, fun t ht => ⟨ho.mem hβ, gf, ?_, ?_⟩⟩
  · intro δ hδ U hu hg
    exact (step δ ((ho.mem hβ).transitive δ hδ) U t).mp
      ((cert t ht).2.2.1 δ (ho.transitive β hβ δ hδ) U hu ((edge δ hδ U).mp hg))
  · exact (step β (fun _ h => h) W t).mp ((cert t ht).2.2.1 β hβ W (fn.bound_l hW).2 hW)

theorem sc_rank_limit_l {ω c X R L V x : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hV : M.mem V X) (rank : Vr_d X L V) (limit : M.IsLimitOrdinal L) (hx : M.mem x V) :
    ∃ β W, M.mem β L ∧ M.mem W X ∧ Vr_d X β W ∧ M.mem x W := by
  obtain ⟨B, F, hB, hF, cert⟩ := rank
  have hxX := hX V hV x hx
  obtain ⟨α, hα, U, hU, hu, sub⟩ := ((cert x hxX).2.2.2).mp hx
  obtain ⟨β, hβ, hαβ⟩ := limit.2.2 α hα
  obtain ⟨W, hW, hw⟩ := (cert V hV).2.1.2.1 β hβ
  exact ⟨β, W, hβ, hX B hB W hW, sc_rank_stage_l hZF hω hX hm theory hV hB hF cert hβ hw,
    ((cert x hxX).2.2.1 β hβ W hW hw).mpr ⟨α, hαβ, U, hU, hu, sub⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 源内部极大滤子的实际子集二择

只在载体的相对幂集中作一次单元素扩张。所需交集和扩张滤子都由
源内有界分离构造，因而不假定整个相对模型满足 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sf_maximal_relative_l {ω c X R : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hn : Nonempty {x // M.mem x X}) (D U P : (rt_model_l X hn).Domain)
    (power : Source_d X D.val P.val) (maximal : Maximal_d (ℳ := rt_model_l X hn) D U) :
    Sf_ultra_d X D.val U.val := by
  let N := rt_model_l X hn
  have sub (A B : N.Domain) : Subset_d (ℳ := N) A B ↔ M.MemberSubset A.val B.val :=
    ⟨fun h x hx => h ⟨x, hX A.val A.property x hx⟩ hx, fun h x hx => h x.val hx⟩
  have inter (A B : N.Domain) : ∃ C : N.Domain, ∀ x : N.Domain, N.mem x C ↔ N.mem x A ∧ N.mem x B := by
    let ρ : Env M 1 := ⟨fun _ => B.val, fun _ => B.val⟩
    let φ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
    obtain ⟨C, hC, hc⟩ := sc_separate_source_l I hZF hω hX hm theory φ (.mem ..) ρ (fun _ => B.property) A.property
    exact ⟨⟨C, hC⟩, fun x => (hc x.val).trans (and_congr_right fun _ => Formula.satisfies_mem_iff _ _ _)⟩
  have adjoin (B : N.Domain) (hB : Subset_d (ℳ := N) B D) : ∃ G : N.Domain,
      IsFilter_d (ℳ := N) D G ∧ Subset_d (ℳ := N) U G ∧ N.mem B G ∧ ∀ t : N.Domain,
      N.mem t G ↔ Subset_d (ℳ := N) t D ∧ ∃ s, N.mem s U ∧ ∀ x, N.mem x s → N.mem x B → N.mem x t := by
    let ρ : Env M 2 := ⟨Fin.cases B.val (fun _ => U.val), fun _ => D.val⟩
    let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 2) (Formula.forallMem .newest
      (.imp (.mem .newest (.bound 3)) (.mem .newest (.bound 2)))) }
    have sat t : φ.denote ρ t ↔ ∃ s, M.mem s U.val ∧ ∀ x, M.mem x s → M.mem x B.val → M.mem x t := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
        Formula.satisfies_imp_iff, Formula.satisfies_mem_iff]; rfl
    obtain ⟨G, hG, spec⟩ := sc_separate_source_l I hZF hω hX hm theory φ
      (.existsMem _ (.forallMem _ (.imp (.mem ..) (.mem ..)))) ρ (Fin.cases B.property (fun _ => U.property)) P.property
    have k (t : N.Domain) : M.mem t.val G ↔ Subset_d (ℳ := N) t D ∧
        ∃ s : N.Domain, N.mem s U ∧ ∀ x : N.Domain, N.mem x s → N.mem x B → N.mem x t := by
      rw [spec t.val, sat t.val, power t.val]
      constructor
      · rintro ⟨⟨_, ht⟩, s, hs, h⟩
        exact ⟨(sub t D).mpr ht, ⟨s, hX U.val U.property s hs⟩, hs, fun x hx hb => h x.val hx hb⟩
      · rintro ⟨ht, s, hs, h⟩
        exact ⟨⟨t.property, (sub t D).mp ht⟩, s.val, hs, fun x hx hb =>
          h ⟨x, hX s.val s.property x hx⟩ hx hb⟩
    refine ⟨⟨G, hG⟩, ⟨fun t ht => ((k t).mp ht).1,
      (k D).mpr ⟨fun _ hx => hx, D, maximal.1.2.1, fun _ hx _ => hx⟩, ?_, ?_⟩,
      fun s hs => (k s).mpr ⟨maximal.1.1 s hs, s, hs, fun _ hx _ => hx⟩,
      (k B).mpr ⟨hB, D, maximal.1.2.1, fun _ _ hx => hx⟩, k⟩
    · intro s t hs hst ht
      obtain ⟨r, hr, h⟩ := ((k s).mp hs).2
      exact (k t).mpr ⟨ht, r, hr, fun x hx hb => hst x (h x hx hb)⟩
    · intro s t hs ht
      obtain ⟨r, hr, h⟩ := ((k s).mp hs).2
      obtain ⟨q, hq, h'⟩ := ((k t).mp ht).2
      obtain ⟨v, hv, vr, vq⟩ := maximal.1.2.2.2 r q hr hq
      obtain ⟨w, hw⟩ := inter v B
      exact ⟨w, (k w).mpr ⟨fun x hx => hB x ((hw x).mp hx).2, v, hv, fun x hx hb => (hw x).mpr ⟨hx, hb⟩⟩,
        fun x hx => h x (vr x ((hw x).mp hx).1) ((hw x).mp hx).2,
        fun x hx => h' x (vq x ((hw x).mp hx).1) ((hw x).mp hx).2⟩
  have decides (A B : N.Domain) (ha : Subset_d (ℳ := N) A D)
      (hb : ∀ x, N.mem x B ↔ N.mem x D ∧ ¬ N.mem x A) : N.mem A U ∨ N.mem B U := by
    rcases Classical.em (N.mem B U) with h | h
    · exact Or.inr h
    · obtain ⟨G, hg, ug, ag, spec⟩ := adjoin A ha
      exact Or.inl (maximal.2.2 G hg (adjoin_proper_d maximal.1 hb spec h) ug A ag)
  have base : Base_d (ℳ := M) D.val U.val := by
    refine ⟨fun A hA => (sub ⟨A, hX U.val U.property A hA⟩ D).mp (maximal.1.1 _ hA), maximal.1.2.1, ?_⟩
    intro A B ha hb
    obtain ⟨C, hc, ca, cb⟩ := maximal.1.2.2.2 ⟨A, hX U.val U.property A ha⟩ ⟨B, hX U.val U.property B hb⟩ ha hb
    exact ⟨C.val, hc, (sub C _).mp ca, (sub C _).mp cb⟩
  refine ⟨base, ?_, ?_, ?_⟩
  · intro A ha
    obtain ⟨x, hx⟩ := maximal.2.1 ⟨A, hX U.val U.property A ha⟩ ha
    exact ⟨x.val, hx⟩
  · intro A B ha hb bd ab
    exact maximal.1.2.2.1 ⟨A, hX U.val U.property A ha⟩ ⟨B, hb⟩ ha ((sub _ _).mpr ab) ((sub _ _).mpr bd)
  · intro A B ha ad hb spec
    exact decides ⟨A, ha⟩ ⟨B, hb⟩ ((sub _ _).mpr ad) (fun x => spec x.val)

end YesMetaZFC.SetTheory.Internal

/-! ## 初始秩模型中的全部不可达层枚举

原内部不可达性先由实际秩闭包读成背景不可达性。严格小秩层的原基数界
给出支撑以下的双射，整个支撑层用支撑自身枚举；所有图再由秩界回收。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem sc_v_rank_size_l (hZFC : M.Models ZFC) {δ X ω L : M.Domain} (hω : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X)
    (h : Sc_inaccessible_d ω X L) : Sc_rank_size_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) X L := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := v_transitive_l I hX
  obtain ⟨above, hr, hs⟩ := sc_v_inaccessible_up_l (ZF.modelsKP hZF) hδ hX h
  obtain ⟨_, hL, _⟩ := h
  have hLδ := ZF.v_ordinal_height_l hZF hX hr.isCardinal.1 hL
  have history {α W} (ha : M.mem α δ) (hw : V_d I α W) : M.mem W X ∧ Vr_d X α W := by
    obtain ⟨B, F, hB, hF, cert, _⟩ := vr_source_l hZF hX hδ ha hw
    exact ⟨ZF.v_mem_l I hZF hw hX ha, B, F, hB, hF, fun t _ => cert t⟩
  have owned {μ W f} (hμ : M.mem μ X) (hW : M.mem W X) (bf : M.IsSetBijectionFromTo I f μ W) : M.mem f X := by
    obtain ⟨B, hB, μb, wb⟩ := v_joint_bound_l I hX hμ hW
    exact v_relation_mem_l I hX hδ hB (fun p hp => by
      obtain ⟨a, ha, b, hb, pair⟩ := (fn0_of_function_l (ZF.modelsKP hZF) bf.1.1).1 p hp
      exact ⟨a, μb a ha, b, wb b hb, pair⟩)
  obtain ⟨W, hw⟩ := ZF.v_exists_l I hZF hr.isCardinal.1
  obtain ⟨hW, rank⟩ := history hLδ hw
  obtain ⟨f, bf⟩ := ZFC.inaccessible_enumeration_l I hZFC hω above hr hs hw
  refine ⟨⟨W, f, hW, rank, owned hL hW bf, bf⟩, fun α hα => ?_⟩
  obtain ⟨W, hw⟩ := ZF.v_exists_l I hZF (hr.isCardinal.1.mem hα)
  obtain ⟨hW, rank⟩ := history (hδ.1.transitive L hLδ α hα) hw
  obtain ⟨ξ, hξ, bound⟩ := ZFC.inaccessible_level_small_l I hZFC hω above hr hs hα hw
  obtain ⟨μ, f, hμ, _, bf⟩ := ZF.small_enumeration_l I hZF hr.isCardinal hξ bound
  exact ⟨W, μ, f, hW, rank, hμ, owned (ht L hL μ hμ) hW bf, bf⟩

theorem sc_v_inaccessible_closure_l (hZFC : M.Models ZFC) {δ X ω : M.Domain} (hω : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) :
    Sc_inaccessible_closure_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X :=
  fun _ h => ⟨sc_regular_l (ZFC.models_zf_l hZFC)
    (sc_v_inaccessible_up_l (ZF.modelsKP (ZFC.models_zf_l hZFC)) hδ hX h).2.1 X, sc_v_rank_size_l hZFC hω hδ hX h⟩

end YesMetaZFC.SetTheory.Internal
