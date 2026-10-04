import YesMetaZFC.SetTheory.LargeCardinal.DerivedFilter

/-! # 派生测度的有界真值集合

在源中实际分离真值集合；其测度值恰等于像公式在种子处的真值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ed_separate_delta_l (hZF : M.Models ZF) {ω X C Y E j D D' P a U}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X C Y E j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hP : M.IsPowerSetOf P D) (hPX : M.MemberSubset P X) (hjD : M.PairMember I D D' j) (ha : M.mem a D')
    (hU : Ed_filter_d I j a D U) {n} (φ : Delta0UnarySchema n) (ρ η : Env M n)
    (hp : ∀ i, M.PairMember I (ρ.bound i) (η.bound i) j) : ∃ A, M.mem A X ∧
      (∀ s, M.mem s A ↔ M.mem s D ∧ φ.toUnarySchema.denote ρ s) ∧
      (M.mem A U ↔ φ.toUnarySchema.denote η a) := by
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  obtain ⟨A, hs⟩ := ZF.separation_exists_d hZF φ.toUnarySchema ρ D
  have hAD : M.MemberSubset A D := fun s ht => ((hs s).mp ht).1
  have hAX := hPX A ((hP A).mpr hAD)
  obtain ⟨A', _, hjA⟩ := hj.2.2 A hAX
  let e : Fin (n + 1) → Fin (n + 3) := Fin.cases 0 (fun i => ⟨i.val + 3, by omega⟩)
  let ψ : Formula 1 (n + 2) := Formula.forallMem .newest
    (.iff (.mem .newest (.bound 2)) (φ.body.rename e))
  have eq (ρ : Env M n) A D s : (((ρ.push A).push D).push s).reindex e = ρ.push s := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩
  have sat (ρ : Env M n) A D : Formula.satisfies ((ρ.push A).push D) ψ ↔
      ∀ s, M.mem s D → (M.mem s A ↔ φ.toUnarySchema.denote ρ s) := by
    simp only [ψ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_rename, eq]; rfl
  have tr := spred_delta_l I hZF hω h hX hY ψ
    (by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed, φ.freeClosed])
    (.forallMem _ (.iff (.mem _ _) (φ.delta0.rename_l e))) ((ρ.push A).push D) ((η.push A').push D')
    (Fin.cases hjD (Fin.cases hjA hp))
  have read := (sat η A' D').mp (tr.mp ((sat ρ A D).mpr fun s hd => (hs s).trans
    ⟨And.right, fun hh => ⟨hd, hh⟩⟩)) a ha
  exact ⟨A, hAX, hs, (ed_filter_member_l I hj.1 hU hAD hjA).trans read⟩

end YesMetaZFC.SetTheory.LargeCardinal
