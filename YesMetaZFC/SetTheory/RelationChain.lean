import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.SetTheory.Definitional.Project.Predicate

/-! # 可定义传递关系的内部 ω 链

沿真实函数图的相邻关系，经原公式分离与内部自然数归纳传播到全部较早指标。
传递性只要求在给定值域上成立；不假定模型的 ω 在外部良基或标准。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rel_chain_l (hZF : M.Models ZF) {n} (φ : BinarySchema n) (ρ : Env M n)
    {ω P Q} (hω : M.IsOmega ω) (hQ : M.IsSetFunctionFromTo I Q ω P)
    (ht : ∀ x y z, M.mem x P → M.mem y P → M.mem z P →
      φ.denote ρ x y → φ.denote ρ y z → φ.denote ρ x z)
    (hs : ∀ i j x y, M.SuccessorOf j i → M.PairMember I i x Q → M.PairMember I j y Q → φ.denote ρ x y) :
    ∀ i j x y, M.mem i j → M.PairMember I i x Q → M.PairMember I j y Q → φ.denote ρ x y := by
  let e : Fin n → Term (n+5) := fun k => .bound ⟨k.val+5, by omega⟩
  let ψ : UnarySchema (n+1) := {
    body := .forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound 3))
      (.imp (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) (.bound 4))
        (.imp (Formula.orderedPairMem 𝒞 (.bound 3) .newest (.bound 4)) (binary_pred_m φ e (.bound 1) .newest))))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, e] }
  have hψ j : ψ.denote (ρ.push Q) j ↔ ∀ i x y,
      M.mem i j → M.PairMember I i x Q → M.PairMember I j y Q → φ.denote ρ x y := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I, binary_pred_sat_l]
    rfl
  have all : ∀ j, M.mem j ω → ∀ i x y,
      M.mem i j → M.PairMember I i x Q → M.PairMember I j y Q → φ.denote ρ x y := by
    apply hω.induction (fun j => ∀ i x y,
      M.mem i j → M.PairMember I i x Q → M.PairMember I j y Q → φ.denote ρ x y)
    · obtain ⟨C, hC⟩ := separation_exists_d hZF ψ (ρ.push Q) ω
      exact ⟨C, fun j => (hC j).trans (and_congr_right fun _ => hψ j)⟩
    · exact fun e he i _ _ hi _ _ => (he i hi).elim
    · intro k hk ih j hj i x y hij hx hy
      obtain ⟨z, hzP, hz⟩ := hQ.2.2 k hk
      rcases (hj i).mp hij with hik | hik
      · exact ht x z y (hQ.output_mem_of_pairMember hx) hzP (hQ.output_mem_of_pairMember hy)
          (ih i x z hik hx hz) (hs k j z y hj hz hy)
      · have he := hZF.1.eq_of_same_members i k hik
        subst i
        have he := hQ.1.2 k x z hx hz
        exact he.symm ▸ hs k j z y hj hz hy
  exact fun i j x y hij hx hy => all j (hQ.input_mem_of_pairMember hy) i x y hij hx hy

end YesMetaZFC.SetTheory.ZF
