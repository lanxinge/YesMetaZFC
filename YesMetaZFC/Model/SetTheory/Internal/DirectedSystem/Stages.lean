import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Limit
import YesMetaZFC.Model.SetTheory.Internal.Isomorphism

/-! # 定向系统分量的实际结构码

分量是标签图的纤维，关系是原分量关系的限制。非空纤维的载体、关系与
结构码均由分离构造；规范投影就是全系统商图在该纤维上的限制。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Di_stage_d (I : kpair_convention_l.Interpretation M) (A p R i c X S : M.Domain) : Prop :=
  Smdl_d I c X S ∧ (∀ x, M.mem x X ↔ M.mem x A ∧ Rd_entry_d x i p) ∧
  ∀ x y, Rd_entry_d x y S ↔ M.mem x X ∧ M.mem y X ∧ Rd_entry_d x y R

def di_stage_m {d} (A p R i c X S : Term d) : Formula 1 d :=
  .conj (smdl_m (𝒞 := kpair_convention_l) c X S) (.conj
    (.forallE (.iff (.mem .newest X.weaken) (.conj (.mem .newest A.weaken) (rd_entry_m .newest i.weaken p.weaken))))
    (.forallE (.forallE (.iff (rd_entry_m (.bound 1) .newest S.weaken.weaken)
      (.conj (.mem (.bound 1) X.weaken.weaken) (.conj (.mem .newest X.weaken.weaken)
        (rd_entry_m (.bound 1) .newest R.weaken.weaken)))))))
derive_free_closed di_stage_m
theorem di_stage_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {d}
    (ρ : Env M d) (A p R i c X S : Term d) : Formula.satisfies ρ (di_stage_m A p R i c X S) ↔
      Di_stage_d I (A.eval ρ) (p.eval ρ) (R.eval ρ) (i.eval ρ) (c.eval ρ) (X.eval ρ) (S.eval ρ) := by
  simp only [di_stage_m, Di_stage_d, Formula.satisfies_conj_iff, smdl_sat_l I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem di_stage_exists_l (hZF : M.Models ZF) {J L A p T R i x : M.Domain}
    (h : Di_system_d J L A p T R) (hx : Rd_entry_d x i p) :
    ∃ c X S, Di_stage_d (kp_pair_l (ZF.modelsKP hZF)) A p R i c X S := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let φ : UnarySchema 2 := { body := rd_entry_m .newest (.bound 1) (.bound 2) }
  obtain ⟨X, hs⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases i (fun _ => p), fun _ => A⟩ A
  have spec y : M.mem y X ↔ M.mem y A ∧ Rd_entry_d y i p :=
    (hs y).trans (and_congr_right fun _ => rd_entry_sat_l hZF.1 _ _ _ _)
  let ψ : BinarySchema 1 := { body := rd_entry_m (.bound 1) .newest (.bound 2) }
  obtain ⟨S, hr, read⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ ⟨fun _ => R, fun _ => R⟩ X
  obtain ⟨c, hc⟩ := I.total X S
  exact ⟨c, X, S, ⟨hc, ⟨x, (spec x).mpr ⟨(h.index.bound_l hx).1, hx⟩⟩, hr⟩, spec,
    fun x y => (read x y).trans (and_congr_right fun _ => and_congr_right fun _ => rd_entry_sat_l hZF.1 _ _ _ _)⟩

/-- 全初等的过渡图；每张图都精确等于原系统在两分量之间的过渡。 -/
def Di_elementary_d (I : kpair_convention_l.Interpretation M) (ω L A p T R : M.Domain) : Prop :=
  ∀ i j c X S d Y V, Di_stage_d I A p R i c X S → Di_stage_d I A p R j d Y V → Rd_entry_d i j L →
    ∃ e, Smap_d I ω c d X Y e ∧ ∀ x y, Rd_entry_d x y e ↔ M.mem x X ∧ M.mem y Y ∧ Rd_entry_d x y T

theorem di_projection_l (hZF : M.Models ZF) {J L A p T R q C V i c X S : M.Domain}
    (h : Di_system_d J L A p T R) (limit : Di_limit_d A p T R q C V)
    (stage : Di_stage_d (kp_pair_l (ZF.modelsKP hZF)) A p R i c X S) :
    ∃ e, M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) e X C ∧
      (∀ x y, Rd_entry_d x y e ↔ M.mem x X ∧ Rd_entry_d x y q) ∧
      ∀ x y u v, Rd_entry_d x u e → Rd_entry_d y v e → (Rd_entry_d x y S ↔ Rd_entry_d u v V) := by
  obtain ⟨Y, e, hy, he, spec, inj, rel⟩ := di_stage_l hZF h limit i
  have eq := hZF.1.eq_of_same_members Y X (fun x => (hy x).trans (stage.2.1 x).symm)
  subst Y
  refine ⟨e, ⟨fn0_function_l (ZF.modelsKP hZF) he, inj⟩, spec, fun x y u v hx hy => ?_⟩
  have read : (M.mem x X ∧ M.mem y X ∧ Rd_entry_d x y R) ↔ Rd_entry_d x y R :=
    ⟨And.right ∘ And.right, fun hr => ⟨(he.bound_l hx).1, (he.bound_l hy).1, hr⟩⟩
  exact (stage.2.2 x y).trans (read.trans (rel x y u v hx hy).symm)

end YesMetaZFC.SetTheory.Internal
