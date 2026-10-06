import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 源内全相对分离得到有界载体上的实际关系

原公式中的无界量词仍在源中解释；载体及有序对图由已有源代数提供。
因此能分离“源中不存在下降枝”等全公式，而不把这种真值误当作绝对真值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_relation_relative_l {ω c X R B : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hn : Nonempty {x // M.mem x X}) {p} (φ : BinarySchema p) (ρ : Env (rt_model_l X hn) p)
    (hB : M.mem B X) : ∃ Q, M.mem Q X ∧ M.IsSetRelationOn I Q B ∧
      ∀ x y : (rt_model_l X hn).Domain, Rd_entry_d x.val y.val Q ↔
        M.mem x.val B ∧ M.mem y.val B ∧ φ.denote ρ x y := by
  obtain ⟨P, hP, product⟩ := theory.algebra.product B B hB hB
  let η := ρ.push ⟨B, hB⟩
  let e : Fin (p+2) → Fin (p+4) := Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ.succ))
  let ψ : UnarySchema (p+1) := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
      (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (φ.body.rename e)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have point (q x y : (rt_model_l X hn).Domain) :
      Formula.satisfies (((η.push q).push x).push y) (φ.body.rename e) ↔ φ.denote ρ x y :=
    (Formula.satisfies_rename ..).trans (Formula.closed_env_l φ.body φ.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
  have pair (q x y : (rt_model_l X hn).Domain) : Formula.satisfies (((η.push q).push x).push y)
      (kpair0_m (.bound 2) (.bound 1) .newest) ↔ KPair_d M q.val x.val y.val :=
    (rt_model_delta_l hX hn (kpair0_delta_l ..) _).trans (kpair0_sat_l hZF.1 ..)
  have sat (q : (rt_model_l X hn).Domain) : ψ.denote η q ↔
      ∃ x : (rt_model_l X hn).Domain, M.mem x.val B ∧ ∃ y : (rt_model_l X hn).Domain,
        M.mem y.val B ∧ KPair_d M q.val x.val y.val ∧ φ.denote ρ x y := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, pair, point]; rfl
  obtain ⟨Q, hQ, sub, spec⟩ := sc_separate_relative_l I hZF hω hm theory hn ψ η hP
  have bounds x y (h : Rd_entry_d x y Q) : M.mem x B ∧ M.mem y B := by
    obtain ⟨q, code, hq⟩ := h
    obtain ⟨a, ha, b, hb, code'⟩ := (product q).mp (sub q hq)
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M code' code
    exact ⟨ha, hb⟩
  refine ⟨Q, hQ, ⟨fun q hq => ((product q).mp (sub q hq)).elim fun x hx =>
    hx.2.elim fun y hy => ⟨x, y, hy.2⟩, bounds⟩, fun x y => ⟨?_, ?_⟩⟩
  · intro h
    obtain ⟨q, code, hq⟩ := h
    obtain ⟨a, ha, b, hb, pair, val⟩ := (sat ⟨q, hX Q hQ q hq⟩).mp ((spec ⟨q, hX Q hQ q hq⟩).mp hq).2
    obtain ⟨ea, eb⟩ := kpair_injective_l M pair code
    have eax : a = x := Subtype.ext ea
    have eby : b = y := Subtype.ext eb
    subst a b
    exact ⟨ha, hb, val⟩
  · rintro ⟨hx, hy, val⟩
    obtain ⟨q, code⟩ := (I).total x.val y.val
    have hq : M.mem q P := (product q).mpr ⟨x.val, hx, y.val, hy, code⟩
    exact ⟨q, code, (spec ⟨q, hX P hP q hq⟩).mpr ⟨hq,
      (sat ⟨q, hX P hP q hq⟩).mpr ⟨x, hx, y, hy, code, val⟩⟩⟩

end YesMetaZFC.SetTheory.Internal
