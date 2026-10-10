import YesMetaZFC.Model.SetTheory.Internal.Structure
import YesMetaZFC.SetTheory.FunctionSpaceConstruction

/-! # 集合编码赋值及单变量更新

变量域 V 和对象域 X 都是内部集合。赋值空间是 X^V 的实际内部函数集；
量词使用覆盖一个坐标的函数图，不在宿主层选择点值或更新函数。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Senv_update_d (f i x g : M.Domain) : Prop :=
  M.IsSetRelation I g ∧ ∀ j y, M.PairMember I j y g ↔
    (j = i ∧ y = x) ∨ (j ≠ i ∧ M.PairMember I j y f)

def senv_update_m {n} (f i x g : Term n) : Formula 1 n :=
  .conj (Formula.isRelation 𝒞 g) (.forallE (.forallE
    (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest g.weaken.weaken)
      (.disj (.conj (Formula.extensionalEq (.bound 1) i.weaken.weaken)
        (Formula.extensionalEq .newest x.weaken.weaken))
        (.conj (.neg (Formula.extensionalEq (.bound 1) i.weaken.weaken))
          (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken))))))
derive_free_closed senv_update_m

theorem senv_update_sat_l (hE : Extensional M) {n} (ρ : Env M n) (f i x g : Term n) :
    Formula.satisfies ρ (senv_update_m (𝒞 := 𝒞) f i x g) ↔
      Senv_update_d I (f.eval ρ) (i.eval ρ) (x.eval ρ) (g.eval ρ) := by
  simp only [senv_update_m, Senv_update_d, Formula.satisfies_conj_iff,
    Formula.satisfies_isRelation_iff I, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_neg_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  rfl

theorem senv_update_unique_l (hE : Extensional M) {f i x g h}
    (hg : Senv_update_d I f i x g) (hh : Senv_update_d I f i x h) : g = h :=
  hg.1.eq_of_pairMember_iff hE hh.1 (fun j y => (hg.2 j y).trans (hh.2 j y).symm)

/-- 任意满足更新方程的图仍是同一变量域上的赋值；不需要选择或额外集合公理。 -/
theorem Senv_update_d.function_l {V X f i x g} (h : Senv_update_d I f i x g)
    (hf : M.IsSetFunctionFromTo I f V X) (hi : M.mem i V) (hx : M.mem x X) :
    M.IsSetFunctionFromTo I g V X := by
  classical
  have range j y (hy : M.PairMember I j y g) : M.mem j V ∧ M.mem y X := by
    rcases (h.2 j y).mp hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · exact ⟨hi, hx⟩
    · exact ⟨hf.input_mem_of_pairMember hy, hf.output_mem_of_pairMember hy⟩
  have total j (hj : M.mem j V) : ∃ y, M.mem y X ∧ M.PairMember I j y g := by
    by_cases he : j = i
    · exact ⟨x, hx, (h.2 j x).mpr (Or.inl ⟨he, rfl⟩)⟩
    · obtain ⟨y, hy, hjy⟩ := hf.2.2 j hj
      exact ⟨y, hy, (h.2 j y).mpr (Or.inr ⟨he, hjy⟩)⟩
  refine ⟨⟨h.1, ?_⟩, fun j => ⟨fun hj => (total j hj).elim fun y h => ⟨y, h.2⟩,
    fun ⟨y, hy⟩ => (range j y hy).1⟩, total⟩
  intro j a b ha hb
  rcases (h.2 j a).mp ha with ⟨he, rfl⟩ | ⟨he, ha⟩ <;>
    rcases (h.2 j b).mp hb with ⟨he', rfl⟩ | ⟨he', hb⟩
  · rfl
  · exact (he' he).elim
  · exact (he he').elim
  · exact hf.1.2 j a b ha hb

/-- 更新模型内赋值并核验函数域和值域；变量域不必是外部可数集。 -/
theorem senv_update_exists_l (hZF : M.Models ZF) {V X f i x}
    (hf : M.IsSetFunctionFromTo I f V X) (hi : M.mem i V) (hx : M.mem x X) :
    ∃ g, Senv_update_d I f i x g ∧ M.IsSetFunctionFromTo I g V X := by
  classical
  let ρ : Env M 3 := ((⟨fun _ => f, fun _ => f⟩ : Env M 1).push i).push x
  let φ : BinarySchema 3 := {
    body := .disj (.conj (Formula.extensionalEq (.bound 1) (.bound 3))
      (Formula.extensionalEq .newest (.bound 2)))
      (.conj (.neg (Formula.extensionalEq (.bound 1) (.bound 3)))
        (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4))) }
  have hφ j y : φ.denote ρ j y ↔ (j = i ∧ y = x) ∨ (j ≠ i ∧ M.PairMember I j y f) := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_neg_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨g, hg, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := V) (target := X)
    (fun j hj => by
      by_cases hji : j = i
      · exact ⟨x, (hφ j x).mpr (Or.inl ⟨hji, rfl⟩)⟩
      · obtain ⟨y, _, hy⟩ := hf.2.2 j hj
        exact ⟨y, (hφ j y).mpr (Or.inr ⟨hji, hy⟩)⟩)
    (by
      intro j _ y z hy hz
      rcases (hφ j y).mp hy with ⟨hji, rfl⟩ | ⟨hji, hy⟩ <;>
        rcases (hφ j z).mp hz with ⟨hji', rfl⟩ | ⟨hji', hz⟩
      · rfl
      · exact (hji' hji).elim
      · exact (hji hji').elim
      · exact hf.1.2 j y z hy hz)
    (fun j y _ hy => ((hφ j y).mp hy).elim (fun h => h.2.symm ▸ hx) (fun h => hf.output_mem_of_pairMember h.2))
  refine ⟨g, ⟨hg.1.1, fun j y => (he j y).trans ?_⟩, hg⟩
  rw [hφ j y]
  exact ⟨And.right, fun h => ⟨h.elim (fun h => h.1.symm ▸ hi) (fun h => hf.input_mem_of_pairMember h.2), h⟩⟩

/-- 非空集合结构的完整赋值空间实际存在且非空。 -/
theorem senv_space_l (hZF : M.Models ZF) (V : M.Domain) {X} (hX : ∃ x, M.mem x X) :
    ∃ E, M.IsFunctionSpace I E V X ∧ ∃ f, M.mem f E := by
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I V X
  obtain ⟨x, hx⟩ := hX
  obtain ⟨f, hf, _⟩ := ZF.exists_constantFunction hZF I (source := V) hx
  exact ⟨E, hE, f, (hE f).mpr hf⟩

end YesMetaZFC.SetTheory.Internal
