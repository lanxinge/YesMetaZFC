import YesMetaZFC.SetTheory.FunctionConstruction
import YesMetaZFC.Model.SetTheory.Internal.Numeral

/-! # 地模型内的集合结构编码

结构码是有序对 (X,R)，其中 X 非空而 R⊆X×X。解码载体是实际子类型，关系
从模型内图逐点读取；不选择载体基点，也不假设解码结构满足外延性或 ZFC。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Smdl_d (c X R : M.Domain) : Prop :=
  I.Codes c X R ∧ (∃ x, M.mem x X) ∧ M.IsSetRelationOn I R X

def smdl_m {n} (c X R : Term n) : Formula 1 n :=
  .conj (𝒞.code c X R) (.conj (.existsE (.mem .newest X.weaken))
    (.conj (Formula.isRelation 𝒞 R) (.forallE (.forallE
      (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken)
        (.conj (.mem (.bound 1) X.weaken.weaken) (.mem .newest X.weaken.weaken)))))))
derive_free_closed smdl_m

theorem smdl_sat_l {n} (ρ : Env M n) (c X R : Term n) :
    Formula.satisfies ρ (smdl_m (𝒞 := 𝒞) c X R) ↔ Smdl_d I (c.eval ρ) (X.eval ρ) (R.eval ρ) := by
  simp only [smdl_m, Smdl_d, Formula.satisfies_conj_iff, I.satisfies_code_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_mem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isRelation_iff I, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  rfl

/-- 编码结构的外部解码与地模型同层，不从非空性消去出 Type 数据。 -/
def smdl_structure_l {X R : M.Domain} (hX : ∃ x, M.mem x X) : Structure.{u} where
  Domain := {x : M.Domain // M.mem x X}
  nonempty := hX.elim (fun x hx => ⟨⟨x, hx⟩⟩)
  mem x y := M.PairMember I x.val y.val R

theorem smdl_unique_l {c X R Y S} (h : Smdl_d I c X R) (k : Smdl_d I c Y S) : X = Y ∧ R = S :=
  I.injective h.1 k.1

/-- 在非空集合上，任意实际二元公式都生成内部关系结构及精确解释证书。 -/
theorem smdl_exists_l (hZF : M.Models ZF) {n} (φ : BinarySchema n) (ρ : Env M n)
    {X} (hX : ∃ x, M.mem x X) : ∃ c R, Smdl_d I c X R ∧
      ∀ x y, M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ φ.denote ρ x y := by
  obtain ⟨R, hR, hr⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ X
  obtain ⟨c, hc⟩ := I.total X R
  exact ⟨c, R, ⟨hc, hX, hR⟩, hr⟩

/-- 任意非空模型内集合的诱导隶属结构，直接作为编码设施的实际实例。 -/
theorem smdl_membership_l (hZF : M.Models ZF) {X} (hX : ∃ x, M.mem x X) :
    ∃ c R, Smdl_d I c X R ∧ ∀ x y,
      M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y := by
  let φ : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  simpa only [BinarySchema.denote, φ, Formula.satisfies_mem_iff,
    Definitional.Term.eval_newest, Term.eval_bound_one_push, Term.eval_bound_zero_push] using
    smdl_exists_l I hZF φ ⟨Fin.elim0, fun _ => X⟩ hX

end YesMetaZFC.SetTheory.Internal
