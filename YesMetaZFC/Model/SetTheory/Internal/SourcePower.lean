import YesMetaZFC.Model.SetTheory.Internal.SourceHierarchy
import YesMetaZFC.SetTheory.CumulativeRelativeClosure
import YesMetaZFC.SetTheory.Filter.Source

/-! # 秩模型的相对幂集闭包

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
  obtain ⟨P, hP, product⟩ := theory.algebra.product D A hD hA
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

theorem sc_v_power_l (hZF : M.Models ZF) {δ V : M.Domain} (hδ : M.IsLimitOrdinal δ)
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ V) : Sc_power_d V := by
  intro A hA
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF A
  exact ⟨P, ZF.v_power_mem_l _ hZF hV hδ hA hp, fun B => (hp B).trans
    ⟨fun sub => ⟨ZF.v_subset_mem_l _ hZF hV hA sub, sub⟩, And.right⟩⟩

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

theorem Sc_power_d.rank_l (hZF : M.Models ZF) {Z α V : M.Domain} (h : Sc_power_d Z)
    (hZ : M.TransitiveSet Z) (hV : M.mem V Z) (rank : Vr_d Z α V) (hα : M.IsLimitOrdinal α) : Sc_power_d V := by
  intro A hA
  obtain ⟨P, hP, spec⟩ := h A (hZ V hV A hA)
  have hPV := rank.subsets_mem_l hZ hV hα hA hP (fun B hB => ((spec B).mp hB).2)
  exact ⟨P, hPV, fun B => ⟨fun hB => ⟨rank.transitive_l hZF hZ hV P hPV B hB, ((spec B).mp hB).2⟩,
    fun ⟨hB, sub⟩ => (spec B).mpr ⟨hZ V hV B hB, sub⟩⟩⟩

end YesMetaZFC.SetTheory.Internal
