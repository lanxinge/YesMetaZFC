import YesMetaZFC.Model.Forcing.Boolean.DenseGround
import YesMetaZFC.Model.Forcing.Embedding.Rank

/-! # 原正锥上的稠密比较及其初等运输

同时保留实际映射、单值性、像的正锥界和该正锥上的稠密性。
该证书由 Kripke 图产生，并可运输到返回模型；不再遗忘泛型正向恢复所需的数据。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}}

structure Dmap_at_d (P R z Q S w F a : M.Domain) : Prop extends Reg_map_d M P R z Q S w F where
  functional : ∀ p x y, Entry_d M p x F → Entry_d M p y F → x = y
  range : ∀ p x, Entry_d M p x F → Below_d M Q S w x a
  dense : ∀ x, Below_d M Q S w x a → ∃ p y, Entry_d M p y F ∧ Entry_d M y x S

def dmap_at_m {n} (P R z Q S w F a : Term n) : Formula 1 n := set[n] ⟪
  (∀ p ∈ ⌜P⌝ₛ, p ≠ ⌜z⌝ₛ → ∃ x, ⌜entry_m⌝ₚ(p,x,⌜F⌝ₛ)) ∧
  (∀ p x, ⌜entry_m⌝ₚ(p,x,⌜F⌝ₛ) → p ∈ ⌜P⌝ₛ ∧ p ≠ ⌜z⌝ₛ ∧ x ∈ ⌜Q⌝ₛ ∧ x ≠ ⌜w⌝ₛ) ∧
  (∀ p q x y, ⌜entry_m⌝ₚ(p,x,⌜F⌝ₛ) → ⌜entry_m⌝ₚ(q,y,⌜F⌝ₛ) →
    ⌜entry_m⌝ₚ(p,q,⌜R⌝ₛ) → ⌜entry_m⌝ₚ(x,y,⌜S⌝ₛ)) ∧
  (∀ p q x y, ⌜entry_m⌝ₚ(p,x,⌜F⌝ₛ) → ⌜entry_m⌝ₚ(q,y,⌜F⌝ₛ) →
    ⌜cmp_m⌝ₚ(⌜Q⌝ₛ,⌜S⌝ₛ,⌜w⌝ₛ,x,y) → ⌜cmp_m⌝ₚ(⌜P⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,p,q)) ∧
  (∀ x ∈ ⌜Q⌝ₛ, x ≠ ⌜w⌝ₛ → ∀ p y, ⌜entry_m⌝ₚ(p,y,⌜F⌝ₛ) → ⌜entry_m⌝ₚ(x,y,⌜S⌝ₛ) →
    ∃ r, r ∈ ⌜P⌝ₛ ∧ r ≠ ⌜z⌝ₛ ∧ ⌜red_m⌝ₚ(⌜R⌝ₛ,⌜Q⌝ₛ,⌜S⌝ₛ,⌜w⌝ₛ,⌜F⌝ₛ,x,r)) ∧
  (∀ p x y, ⌜entry_m⌝ₚ(p,x,⌜F⌝ₛ) → ⌜entry_m⌝ₚ(p,y,⌜F⌝ₛ) → x = y) ∧
  (∀ p x, ⌜entry_m⌝ₚ(p,x,⌜F⌝ₛ) → ⌜below_m⌝ₚ(⌜Q⌝ₛ,⌜S⌝ₛ,⌜w⌝ₛ,x,⌜a⌝ₛ)) ∧
  (∀ x, ⌜below_m⌝ₚ(⌜Q⌝ₛ,⌜S⌝ₛ,⌜w⌝ₛ,x,⌜a⌝ₛ) →
    ∃ p y, ⌜entry_m⌝ₚ(p,y,⌜F⌝ₛ) ∧ ⌜entry_m⌝ₚ(y,x,⌜S⌝ₛ))⟫
derive_free_closed dmap_at_m

theorem dmap_at_sat_l (hE : Extensional M) {n} (ρ : Env M n) (P R z Q S w F a : Term n) :
    Formula.satisfies ρ (dmap_at_m P R z Q S w F a) ↔
      Dmap_at_d (P.eval ρ) (R.eval ρ) (z.eval ρ) (Q.eval ρ) (S.eval ρ) (w.eval ρ) (F.eval ρ) (a.eval ρ) := by
  simp only [dmap_at_m,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff,Formula.extensionalNe,Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hE,entry_sat_l M hE,cmp_sat_l M hE,
    red_sat_l hE,below_sat_l M hE,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h⟩ => ⟨⟨a,b,c,d,e⟩,f,g,h⟩,
    fun h => ⟨h.total,h.domain,h.mono,h.compat,h.reduction,h.functional,h.range,h.dense⟩⟩

theorem Dmap_at_d.image_l {N : Structure.{v}} (hM : Extensional M) (hN : Extensional N)
    (e : M.Domain → N.Domain) (elem : Pe_d e) {P R z Q S w F a : M.Domain}
    (h : Dmap_at_d P R z Q S w F a) : Dmap_at_d (e P) (e R) (e z) (e Q) (e S) (e w) (e F) (e a) := by
  let ρ : Env M 8 := ⟨fun i => [P,R,z,Q,S,w,F,a].get i,fun _ => a⟩
  let φ := dmap_at_m (.bound 0 : Term 8) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)
  exact (dmap_at_sat_l hN (image_env_l e ρ) _ _ _ _ _ _ _ _).mp
    ((elem φ (by simp -implicitDefEqProofs [φ]) ρ).mp ((dmap_at_sat_l hM ρ _ _ _ _ _ _ _ _).mpr h))

/-- 在指定源条件以下提升目标加强；共同加强来自实际相容性反射。 -/
theorem Dmap_at_d.lower_l {P R z Q S w F a p x y : M.Domain} (h : Dmap_at_d P R z Q S w F a)
    (L : Cond_order_d M Q S w) (ha : M.mem a Q) (px : Entry_d M p x F)
    (yx : Below_d M Q S w y x) : ∃ r v, Below_d M P R z r p ∧ Entry_d M r v F ∧ Below_d M Q S w v y := by
  obtain ⟨s,t,st,ty⟩ := h.dense y (below_trans_l L ha yx (h.range p x px))
  have ht := (h.domain s t st).2.2
  have tx := L.trans t y x ht.1 yx.1 (h.domain p x px).2.2.1 ty yx.2.2
  obtain ⟨r,rs,rp⟩ := h.compat s p t x st px ⟨t,below_refl_l L ht.1 ht.2,tx⟩
  obtain ⟨v,rv⟩ := h.total r rs.1 rs.2.1
  have hv := (h.domain r v rv).2.2
  exact ⟨r,v,⟨rs.1,rs.2.1,rp⟩,rv,hv.1,hv.2,
    L.trans v t y hv.1 ht.1 yx.1 (h.mono r s v t rv st rs.2.2) ty⟩

end YesMetaZFC.Model.Forcing.Internal
