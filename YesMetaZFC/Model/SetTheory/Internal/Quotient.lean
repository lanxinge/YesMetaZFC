import YesMetaZFC.Model.SetTheory.Internal.Structure
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 集合关系的规范商及下降映射

等价类由分离形成，全部类由替换收集。泛性质直接构造唯一的内部函数图，
不选择代表元，也不引入对象层选择公理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure Qt_equiv_d (A E : M.Domain) : Prop where
  refl : ∀ x, M.mem x A → Rd_entry_d x x E
  symm : ∀ x y, Rd_entry_d x y E → Rd_entry_d y x E
  trans : ∀ x y z, Rd_entry_d x y E → Rd_entry_d y z E → Rd_entry_d x z E

def Qt_class_d (A E x B : M.Domain) : Prop := ∀ y, M.mem y B ↔ M.mem y A ∧ Rd_entry_d x y E

def qt_class_m {d} (A E x B : Term d) : Formula 1 d := .forallE (.iff (.mem .newest B.weaken)
  (.conj (.mem .newest A.weaken) (rd_entry_m x.weaken .newest E.weaken)))
derive_free_closed qt_class_m

theorem qt_class_sat_l (hE : Extensional M) {d} (ρ : Env M d) (A E x B : Term d) :
    Formula.satisfies ρ (qt_class_m A E x B) ↔ Qt_class_d (A.eval ρ) (E.eval ρ) (x.eval ρ) (B.eval ρ) := by
  simp only [qt_class_m, Qt_class_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

structure Qt_map_d (A E q C : M.Domain) : Prop where
  function : Fn0_d A C q
  range : ∀ B, M.mem B C ↔ ∃ x, Rd_entry_d x B q
  classes : ∀ x B, Rd_entry_d x B q ↔ M.mem x A ∧ Qt_class_d A E x B

theorem qt_map_exists_l (hZF : M.Models ZF) (A E : M.Domain) : ∃ q C, Qt_map_d A E q C := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 2 := (⟨fun _ => A, fun _ => A⟩ : Env M 1).push E
  let φ : BinarySchema 2 := { body := qt_class_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat x B : φ.denote ρ x B ↔ Qt_class_d A E x B := qt_class_sat_l hZF.1 _ _ _ _ _
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF A
  obtain ⟨q, hq, hq'⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := P)
    (by
      intro x _
      let ψ : UnarySchema 2 := { body := rd_entry_m (.bound 1) .newest (.bound 2) }
      obtain ⟨B, hB⟩ := ZF.separation_exists_d hZF ψ ⟨Fin.cases x (fun _ => E), fun _ => A⟩ A
      exact ⟨B, (sat x B).mpr fun y => (hB y).trans (and_congr_right fun _ => rd_entry_sat_l hZF.1 _ _ _ _)⟩)
    (fun x _ B C hB hC => hZF.1.eq_of_same_members B C fun y => ((sat x B).mp hB y).trans ((sat x C).mp hC y).symm)
    (fun x B _ hB => (hP B).mpr fun y hy => (((sat x B).mp hB y).mp hy).1)
  obtain ⟨C, hC⟩ := ZF.exists_range_of_setFunction hZF I hq.1 hq.2.1
  have fn : M.IsSetFunctionFromTo I q A C := ⟨hq.1, hq.2.1,
    fun x hx => (hq.2.2 x hx).imp fun B hB => ⟨(hC B).mpr ⟨x, hB.2⟩, hB.2⟩⟩
  exact ⟨q, C, fn0_of_function_l (ZF.modelsKP hZF) fn, hC,
    fun x B => (hq' x B).trans (and_congr_right fun _ => sat x B)⟩

theorem Qt_map_d.kernel_l (hE : Extensional M) {A E q C x y B D : M.Domain}
    (h : Qt_map_d A E q C) (he : Qt_equiv_d A E) (hx : Rd_entry_d x B q) (hy : Rd_entry_d y D q) :
    B = D ↔ Rd_entry_d x y E := by
  obtain ⟨hxA, hB⟩ := (h.classes x B).mp hx
  obtain ⟨hyA, hD⟩ := (h.classes y D).mp hy
  refine ⟨fun e => ((hB y).mp (e.symm ▸ (hD y).mpr ⟨hyA, he.refl y hyA⟩)).2, fun hxy => ?_⟩
  apply hE.eq_of_same_members B D
  intro z
  exact (hB z).trans ((and_congr_right fun _ =>
    ⟨he.trans y x z (he.symm x y hxy), he.trans x y z hxy⟩).trans (hD z).symm)

/-- 任何在等价类上为常值的实际函数，都唯一地通过商映射分解。 -/
theorem qt_descend_l (hZF : M.Models ZF) {A q C Y f : M.Domain} (hq : Fn0_d A C q)
    (hr : ∀ B, M.mem B C → ∃ x, Rd_entry_d x B q) (hf : Fn0_d A Y f)
    (hc : ∀ x y B u v, Rd_entry_d x B q → Rd_entry_d y B q →
      Rd_entry_d x u f → Rd_entry_d y v f → u = v) :
    ∃ g, Fn0_d C Y g ∧ (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y g) ∧
      ∀ k, Fn0_d C Y k → (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y k) → k = g := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 2 := (⟨fun _ => q, fun _ => q⟩ : Env M 1).push f
  let φ : BinarySchema 2 := { body := .existsE (.conj (rd_entry_m .newest (.bound 2) (.bound 4))
    (rd_entry_m .newest (.bound 1) (.bound 3))) }
  have sat B y : φ.denote ρ B y ↔ ∃ x, Rd_entry_d x B q ∧ Rd_entry_d x y f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨g, hg, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := Y)
    (fun B hB => by
      obtain ⟨x, hx⟩ := hr B hB
      obtain ⟨y, _, hxy⟩ := hf.2.1 x (hq.bound_l hx).1
      exact ⟨y, (sat B y).mpr ⟨x, hx, hxy⟩⟩)
    (fun B _ u v hu hv => by
      obtain ⟨x, hx, hxu⟩ := (sat B u).mp hu
      obtain ⟨y, hy, hyv⟩ := (sat B v).mp hv
      exact hc x y B u v hx hy hxu hyv)
    (fun B y _ hy => ((sat B y).mp hy).elim fun _ hx => (hf.bound_l hx.2).2)
  have fn := fn0_of_function_l (ZF.modelsKP hZF) hg
  have law x B y (hx : Rd_entry_d x B q) (hy : Rd_entry_d x y f) : Rd_entry_d B y g :=
    (spec B y).mpr ⟨(hq.bound_l hx).2, (sat B y).mpr ⟨x, hx, hy⟩⟩
  refine ⟨g, fn, law, fun k hk hkq => hk.ext_l hZF.1 fn ?_⟩
  intro B hB
  obtain ⟨x, hx⟩ := hr B hB
  obtain ⟨y, _, hy⟩ := hf.2.1 x (hq.bound_l hx).1
  exact ⟨y, hkq x B y hx hy, law x B y hx hy⟩

end YesMetaZFC.SetTheory.Internal
