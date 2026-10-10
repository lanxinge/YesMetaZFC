import YesMetaZFC.Model.SetTheory.LevyReflection.Relativization
import YesMetaZFC.Model.SetTheory.Internal.Membership

/-! # 相对化真值与实际内部隶属结构

传递性保证外延等同、子集这两个生产定义原子的绝对性。量词则逐值限制到
载体，因而有限反射可直接作用于已有的实际结构码，无须另交语义对应假设。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
variable {c X R : M.Domain} (hM : Smdl_d I c X R)
  (hR : ∀ x y, M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y)
  (hX : M.TransitiveSet X)
local notation "L" => smdl_structure_l I (R := R) (And.left (And.right hM))
include hR hX

private theorem lr_subset_decode_l (a b : (L).Domain) : M.MemberSubset a.val b.val ↔ (L).MemberSubset a b := by
  constructor
  · exact fun h x hx => (smem_member_l I hM hR x b).mpr (h x.val ((smem_member_l I hM hR x a).mp hx))
  · intro h x hx
    let y : (L).Domain := ⟨x, hX a.val a.property x hx⟩
    exact (smem_member_l I hM hR y b).mp (h y ((smem_member_l I hM hR y a).mpr hx))

private theorem lr_equal_decode_l (a b : (L).Domain) : M.SameMembers a.val b.val ↔ (L).SameMembers a b := by
  have split (K : Structure) (a b : K.Domain) : K.SameMembers a b ↔ K.MemberSubset a b ∧ K.MemberSubset b a :=
    ⟨fun h => ⟨fun x => (h x).mp, fun x => (h x).mpr⟩, fun h x => ⟨h.1 x, h.2 x⟩⟩
  exact (split M a.val b.val).trans ((and_congr (lr_subset_decode_l I hM hR hX a b)
    (lr_subset_decode_l I hM hR hX b a)).trans (split L a b).symm)

theorem lr_rel_decode_l {n d} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (η : Env L n) (θ : Env M d) (T : Term d) (e : Fin n → Term d)
    (hT : T.eval θ = X) (he : ∀ i, (e i).eval θ = (η.bound i).val) :
    Formula.satisfies θ (lr_rel_m φ T e) ↔ Formula.satisfies η φ := by
  have term {n d} (η : Env L n) (θ : Env M d) (e : Fin n → Term d)
      (he : ∀ i, (e i).eval θ = (η.bound i).val) (t : Term n) (ht : t.freeSupport = []) :
      (t.bind e).eval θ = (t.eval η).val := by
    cases t with
    | free _ => simp at ht
    | bound i => exact he i
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => simp only [lr_rel_m, Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff]
  case mem s t =>
    simp only [lr_rel_m, Formula.satisfies_mem_iff, term η θ e he s hφ.1, term η θ e he t hφ.2]
    exact (smem_member_l I hM hR (s.eval η) (t.eval η)).symm
  case atom r hr ts =>
    cases r
    · simpa only [lr_rel_m, Formula.satisfies_atom_extensionalEq_iff, Definitional.TermVector.get_bind, Structure.SameMembers,
        term η θ e he (ts 0) (hφ 0), term η θ e he (ts 1) (hφ 1)] using
        lr_equal_decode_l I hM hR hX ((ts 0).eval η) ((ts 1).eval η)
    · simpa only [lr_rel_m, Formula.satisfies_atom_subset_iff, Definitional.TermVector.get_bind, Structure.MemberSubset,
        term η θ e he (ts 0) (hφ 0), term η θ e he (ts 1) (hφ 1)] using
        lr_subset_decode_l I hM hR hX ((ts 0).eval η) ((ts 1).eval η)
  case neg φ ih =>
    rw [lr_rel_m, Formula.satisfies_neg_iff, Formula.satisfies_neg_iff]
    exact not_congr (ih hφ η θ T e hT he)
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    simp only [lr_rel_m, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, ih hφ.1 η θ T e hT he, jh hφ.2 η θ T e hT he]
  case existsE φ ih | forallE φ ih =>
    have tr (x : (L).Domain) := ih hφ (η.push x) (θ.push x.val) T.weaken
      (Fin.cases .newest (fun i => (e i).weaken)) (by simpa using hT)
      (Fin.cases rfl (fun i => (Definitional.Term.eval_weaken θ x.val (e i)).trans (he i)))
    first
    | rw [lr_rel_m, Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff, hT]
      exact ⟨fun ⟨x, hx, hh⟩ => ⟨⟨x, hx⟩, (tr ⟨x, hx⟩).mp hh⟩,
        fun ⟨x, hx⟩ => ⟨x.val, x.property, (tr x).mpr hx⟩⟩
    | rw [lr_rel_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, hT]
      exact ⟨fun h x => (tr x).mp (h x.val x.property), fun h x hx => (tr ⟨x, hx⟩).mpr (h ⟨x, hx⟩)⟩

/-- 反射层的原真值与其实际内部结构的原真值一致，参数可任意变化。 -/
theorem lr_model_l {n} (φ : Formula 1 n) (hφ : φ.FreeClosed) (h : Lr_reflect_d φ X)
    (ρ : Env M n) (η : Env L n) (he : ∀ i, ρ.bound i = (η.bound i).val) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ :=
  (h ρ (fun i => (he i).symm ▸ (η.bound i).property)).trans
    (lr_rel_decode_l I hM hR hX φ hφ η (ρ.push X) .newest (fun i => .bound i.succ) rfl he)

end YesMetaZFC.SetTheory
