import YesMetaZFC.SetTheory.FlatPairing.Finite
import YesMetaZFC.Model.SetTheory.Internal.Support

/-! # 以有限前缀为坐标的平坦真值表

表直接记录 (程序行, 前缀编码)，不再把赋值集合逐行嵌入函数图。
四条语义方程只量化单份赋值和编码轨道，均可放进一个后继秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ft_arg_d (k : Nat) (ω X R b T f p i j : M.Domain) : Prop := match k with
  | 0 => ∃ x y, M.PairMember I i x f ∧ M.PairMember I j y f ∧ M.PairMember I x y R
  | 1 => ∃ x, M.PairMember I i x f ∧ M.PairMember I j x f
  | 2 => ¬ (M.PairMember I i p T ∨ M.PairMember I j p T)
  | _ => ∃ x g q, M.mem x X ∧ Senv_update_d I f i x g ∧ Fs_code_d I ω X g b q ∧ M.PairMember I j q T

def ft_arg_m (k : Nat) {d} (ω X R b T f p i j : Term d) : Formula 1 d := match k with
  | 0 => .existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 i.weaken.weaken (.bound 1) f.weaken.weaken)
    (.conj (Formula.orderedPairMem 𝒞 j.weaken.weaken .newest f.weaken.weaken)
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken))))
  | 1 => .existsE (.conj (Formula.orderedPairMem 𝒞 i.weaken .newest f.weaken)
    (Formula.orderedPairMem 𝒞 j.weaken .newest f.weaken))
  | 2 => .neg (.disj (Formula.orderedPairMem 𝒞 i p T) (Formula.orderedPairMem 𝒞 j p T))
  | _ => .existsE (.existsE (.existsE (.conj (.mem (.bound 2) X.weaken.weaken.weaken) (.conj
    (senv_update_m (𝒞 := 𝒞) f.weaken.weaken.weaken i.weaken.weaken.weaken (.bound 2) (.bound 1)) (.conj
    (fs_code_m (𝒞 := 𝒞) ω.weaken.weaken.weaken X.weaken.weaken.weaken (.bound 1) b.weaken.weaken.weaken .newest)
    (Formula.orderedPairMem 𝒞 j.weaken.weaken.weaken .newest T.weaken.weaken.weaken))))))
@[simp] theorem ft_arg_closed_l (k : Nat) {d} (ω X R b T f p i j : Term d)
    (hω : ω.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hb : b.freeSupport = []) (hT : T.freeSupport = []) (hf : f.freeSupport = [])
    (hp : p.freeSupport = []) (hi : i.freeSupport = []) (hj : j.freeSupport = []) :
    (ft_arg_m (𝒞 := 𝒞) k ω X R b T f p i j).FreeClosed := by
  rcases k with _ | (_ | (_ | k)) <;>
    simp -implicitDefEqProofs [ft_arg_m, Definitional.Formula.FreeClosed, hω, hX, hR, hb, hT, hf, hp, hi, hj]

theorem ft_arg_sat_l (hE : Extensional M) (k : Nat) {d} (ρ : Env M d) (ω X R b T f p i j : Term d) :
    Formula.satisfies ρ (ft_arg_m (𝒞 := 𝒞) k ω X R b T f p i j) ↔
      Ft_arg_d I k (ω.eval ρ) (X.eval ρ) (R.eval ρ) (b.eval ρ) (T.eval ρ)
        (f.eval ρ) (p.eval ρ) (i.eval ρ) (j.eval ρ) := by
  rcases k with _ | (_ | (_ | k)) <;>
    simp only [ft_arg_m, Ft_arg_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_neg_iff, Formula.satisfies_disj_iff,
      Formula.satisfies_mem_iff, senv_update_sat_l I hE, fs_code_sat_l I hE,
      Definitional.Term.eval_weaken, Definitional.Term.eval_newest] <;> rfl

def Ft_node_d (ω X R b T c f p : M.Domain) : Prop :=
  ∃ k : Fin 4, ∃ i j, Sop_d I k.val c i j ∧ Ft_arg_d I k.val ω X R b T f p i j

private def ft_case_m (k : Nat) {d} (ω X R b T c f p : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (sop_m (𝒞 := 𝒞) k c.weaken.weaken (.bound 1) .newest)
  (ft_arg_m (𝒞 := 𝒞) k ω.weaken.weaken X.weaken.weaken R.weaken.weaken b.weaken.weaken T.weaken.weaken
    f.weaken.weaken p.weaken.weaken (.bound 1) .newest)))
derive_free_closed ft_case_m

def ft_node_m {d} (ω X R b T c f p : Term d) : Formula 1 d := .disj
  (ft_case_m (𝒞 := 𝒞) 0 ω X R b T c f p) (.disj (ft_case_m (𝒞 := 𝒞) 1 ω X R b T c f p)
    (.disj (ft_case_m (𝒞 := 𝒞) 2 ω X R b T c f p) (ft_case_m (𝒞 := 𝒞) 3 ω X R b T c f p)))
derive_free_closed ft_node_m

theorem ft_node_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X R b T c f p : Term d) :
    Formula.satisfies ρ (ft_node_m (𝒞 := 𝒞) ω X R b T c f p) ↔
      Ft_node_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (b.eval ρ) (T.eval ρ) (c.eval ρ) (f.eval ρ) (p.eval ρ) := by
  simp only [ft_node_m, Ft_node_d, Fin.exists_fin_succ, Fin.exists_fin_zero, or_false, ft_case_m,
    Formula.satisfies_disj_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sop_sat_l I, ft_arg_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

theorem ft_node_decode_l (hKP : M.Models KP) {ω X R b T c f p i j} (k : Fin 4) (hs : Sop_d I k.val c i j) :
    Ft_node_d I ω X R b T c f p ↔ Ft_arg_d I k.val ω X R b T f p i j := by
  refine ⟨?_, fun h => ⟨k, i, j, hs, h⟩⟩
  rintro ⟨l, a, d, ht, h⟩
  obtain ⟨eq, rfl, rfl⟩ := sop_injective_l I hKP hs ht
  have kl : k = l := Fin.ext eq
  exact kl ▸ h

def Ft_eval_d (ω X R b F n T : M.Domain) : Prop := M.IsSetRelation I T ∧
  (∀ r p, M.PairMember I r p T → M.mem r n ∧
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧ Fs_code_d I ω X f b p) ∧
  ∀ r c f p, M.PairMember I r c F → M.IsSetFunctionFromTo I f ω X → Fs_code_d I ω X f b p →
    (M.PairMember I r p T ↔ Ft_node_d I ω X R b T c f p)

def ft_eval_m {d} (ω X R b F n T : Term d) : Formula 1 d := .conj (Formula.isRelation 𝒞 T) (.conj
  (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest T.weaken.weaken)
    (.conj (.mem (.bound 1) n.weaken.weaken) (.existsE (.conj
      (Formula.isFunctionFromTo 𝒞 .newest ω.weaken.weaken.weaken X.weaken.weaken.weaken)
      (fs_code_m (𝒞 := 𝒞) ω.weaken.weaken.weaken X.weaken.weaken.weaken .newest b.weaken.weaken.weaken (.bound 1))))))))
  (.forallE (.forallE (.forallE (.forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 2) F.weaken.weaken.weaken.weaken) (.imp
    (Formula.isFunctionFromTo 𝒞 (.bound 1) ω.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken) (.imp
    (fs_code_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken (.bound 1)
      b.weaken.weaken.weaken.weaken .newest) (.iff
    (Formula.orderedPairMem 𝒞 (.bound 3) .newest T.weaken.weaken.weaken.weaken)
    (ft_node_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
      b.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) .newest))))))))))
derive_free_closed ft_eval_m

theorem ft_eval_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X R b F n T : Term d) :
    Formula.satisfies ρ (ft_eval_m (𝒞 := 𝒞) ω X R b F n T) ↔
      Ft_eval_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (b.eval ρ) (F.eval ρ) (n.eval ρ) (T.eval ρ) := by
  simp only [ft_eval_m, Ft_eval_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    fs_code_sat_l I hE, Formula.satisfies_iff_iff, ft_node_sat_l I hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.Internal
