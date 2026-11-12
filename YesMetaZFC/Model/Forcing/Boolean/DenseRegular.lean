import YesMetaZFC.Model.Forcing.Boolean.DenseMap
import YesMetaZFC.Model.Forcing.Boolean.RegularSet

/-! # 稠密映射沿实际集合图回拉正则开集 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def Rpull_d (P z F U V : M.Domain) : Prop := ∀ p,
  M.mem p V ↔ M.mem p P ∧ p ≠ z ∧ ∃ x, Entry_d M p x F ∧ M.mem x U

def rpull_m {n} (P z F U V : Term n) : Formula 1 n := set[n] ⟪∀ p,
  p ∈ ⌜V⌝ₛ ↔ (p ∈ ⌜P⌝ₛ ∧ p ≠ ⌜z⌝ₛ ∧ (∃ x, ⌜entry_m⌝ₚ(p,x,⌜F⌝ₛ) ∧ x ∈ ⌜U⌝ₛ))⟫
derive_free_closed rpull_m

theorem rpull_sat_l (hE : Extensional M) {n} (ρ : Env M n) (P z F U V : Term n) :
    Formula.satisfies ρ (rpull_m P z F U V) ↔ Rpull_d (P.eval ρ) (z.eval ρ) (F.eval ρ) (U.eval ρ) (V.eval ρ) := by
  simp only [rpull_m,Rpull_d,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_conj_iff,Formula.extensionalNe,Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_exists_iff,entry_sat_l M hE,Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
include hZF

theorem rpull_exists_l (P z F U : M.Domain) : ∃ V, Rpull_d P z F U V := by
  let ρ : Env M 3 := ⟨fun i => [z,F,U].get i,fun _ => P⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪⌜(.newest : Term 4)⌝ₛ ≠ ⌜(.bound 1 : Term 4)⌝ₛ ∧
    (∃ x, ⌜entry_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,x,⌜(.bound 2 : Term 4)⌝ₛ) ∧ x ∈ ⌜(.bound 3 : Term 4)⌝ₛ)⟫ }
  obtain ⟨V,members⟩ := ZF.separation_exists_d hZF φ ρ P
  refine ⟨V,fun p => (members p).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ,Formula.satisfies_conj_iff,Formula.extensionalNe,Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_exists_iff,Formula.satisfies_mem_iff,
    entry_sat_l M hZF.1,Definitional.Term.eval_weaken]
  rfl

omit hZF in
theorem Rpull_d.read_l {P R z Q S w F U V p x : M.Domain} (h : Dmap_d P R z Q S w F)
    (pull : Rpull_d P z F U V) (px : Entry_d M p x F) : M.mem p V ↔ M.mem x U :=
  (pull p).trans ⟨fun ⟨_,_,y,py,hy⟩ => (h.functional p y x py px) ▸ hy,
    fun hx => ⟨(h.domain p x px).1.1,(h.domain p x px).1.2,x,px,hx⟩⟩

omit hZF in
theorem Rpull_d.regular_l {P R z Q S w F U V : M.Domain} (h : Dmap_d P R z Q S w F)
    (L : Cond_order_d M Q S w) (pull : Rpull_d P z F U V)
    (regular : Ropen_d Q S w U) : Ropen_d P R z V := by
  refine ⟨fun p hp => ⟨((pull p).mp hp).1,((pull p).mp hp).2.1⟩,?_,?_⟩
  · intro p q _ hq hp
    obtain ⟨_,_,x,px,hx⟩ := (pull p).mp hp
    obtain ⟨y,qy⟩ := h.total q hq.1 hq.2.1
    have hy := (h.domain q y qy).2
    exact (pull.read_l h qy).mpr (regular.2.1 x y (h.domain p x px).2.1
      ⟨hy.1,hy.2,h.mono q p y x qy px hq.2.2⟩ hx)
  · intro p hp hz dense
    obtain ⟨x,px⟩ := h.total p hp hz
    have hx := (h.domain p x px).2
    apply (pull.read_l h px).mpr
    apply regular.2.2 x hx.1 hx.2
    intro q hq
    obtain ⟨r,y,rp,ry,yq⟩ := h.lower_l L px hq
    obtain ⟨s,sr,sv⟩ := dense r rp
    obtain ⟨t,st⟩ := h.total s sr.1 sr.2.1
    have ht := (h.domain s t st).2
    exact ⟨t,⟨ht.1,ht.2,L.trans t y q ht.1 yq.1 hq.1 (h.mono s r t y st ry sr.2.2) yq.2.2⟩,
      (pull.read_l h st).mp sv⟩

omit hZF in
theorem Rpull_d.order_l {P R z Q S w F U V X Y : M.Domain} (h : Dmap_d P R z Q S w F)
    (L : Cond_order_d M Q S w) (first : Rpull_d P z F U X) (second : Rpull_d P z F V Y)
    (left : Ropen_d Q S w U) (right : Ropen_d Q S w V) : M.MemberSubset X Y ↔ M.MemberSubset U V := by
  constructor
  · intro sub x hx
    have pos := left.1 x hx
    apply right.2.2 x pos.1 pos.2
    intro q hq
    obtain ⟨p,y,py,yq⟩ := h.dense q hq.1 hq.2.1
    have hy := (h.domain p y py).2
    have yu := left.2.1 x y pos.1 ⟨hy.1,hy.2,L.trans y q x hy.1 hq.1 pos.1 yq hq.2.2⟩ hx
    exact ⟨y,⟨hy.1,hy.2,yq⟩,(second.read_l h py).mp (sub p ((first.read_l h py).mpr yu))⟩
  · intro sub p hp
    obtain ⟨hb,hz,x,px,hx⟩ := (first p).mp hp
    exact (second p).mpr ⟨hb,hz,x,px,sub x hx⟩

end YesMetaZFC.Model.Forcing.Internal
