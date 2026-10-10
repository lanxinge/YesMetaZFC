import YesMetaZFC.Model.SetTheory.Internal.Syntax

/-! # 内部满足关系的递归原公式

每行真值是一个赋值集合。关系与等号逐点读取赋值；或非取两真值集之并的补；
存在量词沿单变量更新作投影。递归算子只生成原公式，解的存在性由后续模块证明。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sarg_d (k : Nat) (X R H f i j : M.Domain) : Prop :=
  match k with
  | 0 => ∃ x y, M.PairMember I i x f ∧ M.PairMember I j y f ∧ M.PairMember I x y R
  | 1 => ∃ x, M.PairMember I i x f ∧ M.PairMember I j x f
  | 2 => ∃ A B, M.PairMember I i A H ∧ M.PairMember I j B H ∧ ¬ (M.mem f A ∨ M.mem f B)
  | _ => ∃ A, M.PairMember I j A H ∧ ∃ x g, M.mem x X ∧ Senv_update_d I f i x g ∧ M.mem g A

def sarg_m (k : Nat) {n} (X R H f i j : Term n) : Formula 1 n :=
  match k with
  | 0 => .existsE (.existsE
      (.conj (Formula.orderedPairMem 𝒞 i.weaken.weaken (.bound 1) f.weaken.weaken)
        (.conj (Formula.orderedPairMem 𝒞 j.weaken.weaken .newest f.weaken.weaken)
          (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken))))
  | 1 => .existsE (.conj (Formula.orderedPairMem 𝒞 i.weaken .newest f.weaken)
      (Formula.orderedPairMem 𝒞 j.weaken .newest f.weaken))
  | 2 => .existsE (.existsE
      (.conj (Formula.orderedPairMem 𝒞 i.weaken.weaken (.bound 1) H.weaken.weaken)
        (.conj (Formula.orderedPairMem 𝒞 j.weaken.weaken .newest H.weaken.weaken)
          (.neg (.disj (.mem f.weaken.weaken (.bound 1)) (.mem f.weaken.weaken .newest))))))
  | _ => .existsE (.conj (Formula.orderedPairMem 𝒞 j.weaken .newest H.weaken)
      (.existsE (.existsE (.conj (.mem (.bound 1) X.weaken.weaken.weaken)
        (.conj (senv_update_m (𝒞 := 𝒞) f.weaken.weaken.weaken i.weaken.weaken.weaken (.bound 1) .newest)
          (.mem .newest (.bound 2)))))))
@[simp] theorem sarg_closed_l (k : Nat) {n} (X R H f i j : Term n)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hH : H.freeSupport = [])
    (hf : f.freeSupport = []) (hi : i.freeSupport = []) (hj : j.freeSupport = []) :
    (sarg_m (𝒞 := 𝒞) k X R H f i j).FreeClosed := by
  rcases k with _ | (_ | (_ | k)) <;>
    simp -implicitDefEqProofs [sarg_m, Definitional.Formula.FreeClosed, hX, hR, hH, hf, hi, hj]

theorem sarg_sat_l (hE : Extensional M) (k : Nat) {n} (ρ : Env M n) (X R H f i j : Term n) :
    Formula.satisfies ρ (sarg_m (𝒞 := 𝒞) k X R H f i j) ↔
      Sarg_d I k (X.eval ρ) (R.eval ρ) (H.eval ρ) (f.eval ρ) (i.eval ρ) (j.eval ρ) := by
  rcases k with _ | (_ | (_ | k)) <;>
    simp only [sarg_m, Sarg_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_neg_iff, Formula.satisfies_disj_iff,
      Formula.satisfies_mem_iff, senv_update_sat_l I hE,
      Definitional.Term.eval_weaken, Definitional.Term.eval_newest] <;> rfl

def Snode_d (X R H c f : M.Domain) : Prop :=
  ∃ k : Fin 4, ∃ i j, Sop_d I k.val c i j ∧ Sarg_d I k.val X R H f i j

private def eval_case_m (k : Nat) {n} (X R H c f : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (sop_m (𝒞 := 𝒞) k c.weaken.weaken (.bound 1) .newest)
    (sarg_m (𝒞 := 𝒞) k X.weaken.weaken R.weaken.weaken H.weaken.weaken f.weaken.weaken (.bound 1) .newest)))
derive_free_closed eval_case_m

def snode_m {n} (X R H c f : Term n) : Formula 1 n :=
  .disj (eval_case_m (𝒞 := 𝒞) 0 X R H c f) (.disj (eval_case_m (𝒞 := 𝒞) 1 X R H c f)
    (.disj (eval_case_m (𝒞 := 𝒞) 2 X R H c f) (eval_case_m (𝒞 := 𝒞) 3 X R H c f)))
derive_free_closed snode_m

theorem snode_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R H c f : Term n) :
    Formula.satisfies ρ (snode_m (𝒞 := 𝒞) X R H c f) ↔
      Snode_d I (X.eval ρ) (R.eval ρ) (H.eval ρ) (c.eval ρ) (f.eval ρ) := by
  simp only [snode_m, Snode_d, Fin.exists_fin_succ, Fin.exists_fin_zero, or_false,
    eval_case_m, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, sop_sat_l I, sarg_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 合法构造符唯一决定其语义分支，不能用另一种指令伪造真值。 -/
theorem snode_decode_l (hKP : M.Models KP) {X R H c f i j} (k : Fin 4) (hc : Sop_d I k.val c i j) :
    Snode_d I X R H c f ↔ Sarg_d I k.val X R H f i j := by
  constructor
  · rintro ⟨l, a, b, hd, harg⟩
    obtain ⟨hk, rfl, rfl⟩ := sop_injective_l I hKP hc hd
    have he : k = l := Fin.ext hk
    subst l
    exact harg
  · exact fun h => ⟨k, i, j, hc, h⟩

def Seval_at_d (X R F H f : M.Domain) : Prop :=
  ∃ k c, M.IsDomainOf I k H ∧ M.PairMember I k c F ∧ Snode_d I X R H c f

def seval_at_m {n} (X R F H f : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (Formula.isDomain 𝒞 (.bound 1) H.weaken.weaken)
    (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
      (snode_m (𝒞 := 𝒞) X.weaken.weaken R.weaken.weaken H.weaken.weaken .newest f.weaken.weaken))))
derive_free_closed seval_at_m

theorem seval_at_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R F H f : Term n) :
    Formula.satisfies ρ (seval_at_m (𝒞 := 𝒞) X R F H f) ↔
      Seval_at_d I (X.eval ρ) (R.eval ρ) (F.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [seval_at_m, Seval_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isDomain_iff I, Formula.satisfies_orderedPairMem_iff I, snode_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Seval_step_d (X R E F H Y : M.Domain) : Prop :=
  ∀ f, M.mem f Y ↔ M.mem f E ∧ Seval_at_d I X R F H f

def seval_step_m {n} (X R E F H Y : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest Y.weaken) (.conj (.mem .newest E.weaken)
    (seval_at_m (𝒞 := 𝒞) X.weaken R.weaken F.weaken H.weaken .newest)))
derive_free_closed seval_step_m

theorem seval_step_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R E F H Y : Term n) :
    Formula.satisfies ρ (seval_step_m (𝒞 := 𝒞) X R E F H Y) ↔
      Seval_step_d I (X.eval ρ) (R.eval ρ) (E.eval ρ) (F.eval ρ) (H.eval ρ) (Y.eval ρ) := by
  simp only [seval_step_m, Seval_step_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, seval_at_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def seval_s : BinarySchema 4 := {
  body := seval_step_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }

def seval_env_l (X R E F : M.Domain) : Env M 4 :=
  (((⟨fun _ => X, fun _ => X⟩ : Env M 1).push R).push E).push F

theorem seval_op_l (hE : Extensional M) (ρ : Env M 4) :
    (seval_s (𝒞 := 𝒞)).denote ρ = Seval_step_d I (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) := by
  funext H Y
  exact propext (seval_step_sat_l I hE ((ρ.push H).push Y) _ _ _ _ _ _)

def Seval_d (X R E F n H : M.Domain) : Prop :=
  M.IsRecursiveSequence I (Seval_step_d I X R E F) H n

def seval_m {n} (X R E F l H : Term n) : Formula 1 n :=
  Formula.isRecursiveSequence 𝒞 (seval_s (𝒞 := 𝒞))
    (Definitional.TermVector.ofFn (Fin.cases F (Fin.cases E (Fin.cases R (fun _ => X))))) H l
@[simp] theorem seval_closed_l {n} (X R E F l H : Term n)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hE : E.freeSupport = [])
    (hF : F.freeSupport = []) (hl : l.freeSupport = []) (hH : H.freeSupport = []) :
    (seval_m (𝒞 := 𝒞) X R E F l H).FreeClosed := by
  apply Formula.isRecursiveSequence_freeClosed
  · intro i
    simp only [Definitional.TermVector.get_ofFn]
    exact Fin.cases hF (Fin.cases hE (Fin.cases hR (fun _ => hX))) i
  · exact hH
  · exact hl

theorem seval_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R E F l H : Term n) :
    Formula.satisfies ρ (seval_m (𝒞 := 𝒞) X R E F l H) ↔
      Seval_d I (X.eval ρ) (R.eval ρ) (E.eval ρ) (F.eval ρ) (l.eval ρ) (H.eval ρ) := by
  rw [seval_m, Formula.satisfies_isRecursiveSequence_iff I hE, seval_op_l I hE]
  rfl

end YesMetaZFC.SetTheory.Internal
