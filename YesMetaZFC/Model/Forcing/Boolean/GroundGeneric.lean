import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Order.GlobalDense

/-! # 旧幂集参数下的泛型滤子公式

𝒟 是旧条件域的幂集的规范像，而不是扩张重新计算的幂集。
因此下面的有界稠密集条件精确表达对地模型泛型，允许扩张中出现新子集。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}}

def gn_dense_m {n} (B R z D p : Term n) : Formula 1 n := set[n] ⟪
  ∀ q, ⌜below_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,q,⌜p⌝ₛ) →
    ∃ r, ⌜below_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,r,q) ∧ r ∈ ⌜D⌝ₛ⟫
derive_free_closed gn_dense_m

theorem gn_dense_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z D p : Term n) :
    Formula.satisfies ρ (gn_dense_m B R z D p) ↔
      Dense_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (fun q => M.mem q (D.eval ρ)) (p.eval ρ) := by
  simp only [gn_dense_m,Dense_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    below_sat_l M hE,Definitional.Term.eval_weaken]
  rfl

structure Gset_d (B R z 𝒟 H : M.Domain) : Prop where
  proper : ∀ p, M.mem p H → M.mem p B ∧ p ≠ z
  inhabited : ∃ p, M.mem p H
  upward : ∀ p q, M.mem p H → M.mem q B → Entry_d M p q R → M.mem q H
  directed : ∀ p q, M.mem p H → M.mem q H → ∃ r, M.mem r H ∧ Entry_d M r p R ∧ Entry_d M r q R
  meets : ∀ p, M.mem p H → ∀ D, M.mem D 𝒟 → Dense_d M B R z (fun q => M.mem q D) p →
    ∃ q, M.mem q H ∧ M.mem q D

def gset_m {n} (B R z 𝒟 H : Term n) : Formula 1 n := set[n] ⟪
  (∀ p ∈ ⌜H⌝ₛ, p ∈ ⌜B⌝ₛ ∧ p ≠ ⌜z⌝ₛ) ∧ (∃ p, p ∈ ⌜H⌝ₛ) ∧
  (∀ p ∈ ⌜H⌝ₛ, ∀ q ∈ ⌜B⌝ₛ, ⌜entry_m⌝ₚ(p,q,⌜R⌝ₛ) → q ∈ ⌜H⌝ₛ) ∧
  (∀ p ∈ ⌜H⌝ₛ, ∀ q ∈ ⌜H⌝ₛ, ∃ r, r ∈ ⌜H⌝ₛ ∧ ⌜entry_m⌝ₚ(r,p,⌜R⌝ₛ) ∧ ⌜entry_m⌝ₚ(r,q,⌜R⌝ₛ)) ∧
  (∀ p ∈ ⌜H⌝ₛ, ∀ D ∈ ⌜𝒟⌝ₛ, ⌜gn_dense_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,D,p) → ∃ q, q ∈ ⌜H⌝ₛ ∧ q ∈ D)⟫
derive_free_closed gset_m

theorem gset_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z 𝒟 H : Term n) :
    Formula.satisfies ρ (gset_m B R z 𝒟 H) ↔
      Gset_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (𝒟.eval ρ) (H.eval ρ) := by
  simp only [gset_m,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_mem_iff,Formula.extensionalNe,
    Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hE,Formula.satisfies_imp_iff,
    entry_sat_l M hE,gn_dense_sat_l hE,Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,(fun p q hp hq => h.2.2.1 p hp q hq),
      (fun p q hp hq => h.2.2.2.1 p hp q hq),h.2.2.2.2⟩,
    fun h => ⟨h.proper,h.inhabited,(fun p hp q hq => h.upward p q hp hq),
      (fun p hp q hq => h.directed p q hp hq),h.meets⟩⟩

variable {N : Structure.{v}} (hZF : M.Models ZF) (hN : Extensional N)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ c, M.mem c a ∧ j c = y)
include hZF hN inj full

theorem image_dense_set_l {B R z D p : M.Domain} :
    Dense_d N (j B) (j R) (j z) (fun q => N.mem q (j D)) (j p) ↔
      Dense_d M B R z (fun q => M.mem q D) p := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hZF)) hN
  have below a b : Below_d N (j B) (j R) (j z) (j a) (j b) ↔ Below_d M B R z a b :=
    and_congr (image_member_l j inj full) (and_congr (not_congr inj.eq_iff) (entry a b R).symm)
  constructor
  · intro dense q hq
    obtain ⟨r,hr,hD⟩ := dense (j q) ((below q p).mpr hq)
    obtain ⟨s,_,rfl⟩ := (full B r).mp hr.1
    exact ⟨s,(below s q).mp hr,(image_member_l j inj full).mp hD⟩
  · intro dense q hq
    obtain ⟨a,_,rfl⟩ := (full B q).mp hq.1
    obtain ⟨r,hr,hD⟩ := dense a ((below a p).mp hq)
    exact ⟨j r,(below r a).mpr hr,(image_member_l j inj full).mpr hD⟩

theorem image_gset_l {B R z 𝒟 : M.Domain} {H : N.Domain} {G : M.Domain → Prop}
    (generic : Generic_d M B R z G)
    (values : ∀ x, N.mem x H ↔ ∃ p, G p ∧ j p = x) : Gset_d (j B) (j R) (j z) (j 𝒟) H := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hZF)) hN
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨p,hp,rfl⟩ := (values x).mp hx
    exact ⟨(image_member_l j inj full).mpr (generic.proper p hp).1,
      fun eq => (generic.proper p hp).2 (inj eq)⟩
  · obtain ⟨p,hp⟩ := generic.inhabited
    exact ⟨j p,(values (j p)).mpr ⟨p,hp,rfl⟩⟩
  · intro x y hx hy xy
    obtain ⟨p,hp,rfl⟩ := (values x).mp hx
    obtain ⟨q,hq,rfl⟩ := (full B y).mp hy
    exact (values (j q)).mpr ⟨q,generic.upward p q hp hq ((entry p q R).mpr xy),rfl⟩
  · intro x y hx hy
    obtain ⟨p,hp,rfl⟩ := (values x).mp hx
    obtain ⟨q,hq,rfl⟩ := (values y).mp hy
    obtain ⟨r,hr,rp,rq⟩ := generic.directed p q hp hq
    exact ⟨j r,(values (j r)).mpr ⟨r,hr,rfl⟩,(entry r p R).mp rp,(entry r q R).mp rq⟩
  · intro x hx D hD dense
    obtain ⟨p,hp,rfl⟩ := (values x).mp hx
    obtain ⟨E,_,rfl⟩ := (full 𝒟 D).mp hD
    obtain ⟨q,hq,hE⟩ := generic.meets p hp E ((image_dense_set_l hZF hN j inj full).mp dense)
    exact ⟨j q,(values (j q)).mpr ⟨q,hq,rfl⟩,(image_member_l j inj full).mpr hE⟩

/-- 一个旧全局稠密集的规范像仍全局稠密；不声称扩张没有新稠密集。 -/
theorem image_global_dense_l {B R z D : M.Domain} (dense : Dense_set_d M B R z D) :
    Dense_set_d N (j B) (j R) (j z) (j D) := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hZF)) hN
  constructor
  · intro q hq
    obtain ⟨p,hp,rfl⟩ := (full D q).mp hq
    exact ⟨(image_member_l j inj full).mpr (dense.1 p hp).1,fun eq => (dense.1 p hp).2 (inj eq)⟩
  · intro q hq nz
    obtain ⟨p,hp,rfl⟩ := (full B q).mp hq
    obtain ⟨r,rp,rD⟩ := dense.2 p hp (fun eq => nz (congrArg j eq))
    exact ⟨j r,⟨(image_member_l j inj full).mpr rp.1,fun eq => rp.2.1 (inj eq),(entry r p R).mp rp.2.2⟩,
      (image_member_l j inj full).mpr rD⟩

theorem Gset_d.ground_l {B R z 𝒟 : M.Domain} {H : N.Domain}
    (power : M.IsPowerSetOf 𝒟 B) (h : Gset_d (j B) (j R) (j z) (j 𝒟) H) :
    Generic_d M B R z (fun p => N.mem (j p) H) := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hZF)) hN
  refine ⟨fun p hp => ⟨(image_member_l j inj full).mp (h.proper (j p) hp).1,
    fun eq => (h.proper (j p) hp).2 (congrArg j eq)⟩,?_,?_,?_,?_⟩
  · obtain ⟨x,hx⟩ := h.inhabited
    obtain ⟨p,_,rfl⟩ := (full B x).mp (h.proper x hx).1
    exact ⟨p,hx⟩
  · intro p q hp hq pq
    exact h.upward (j p) (j q) hp ((image_member_l j inj full).mpr hq) ((entry p q R).mp pq)
  · intro p q hp hq
    obtain ⟨r,hr,rp,rq⟩ := h.directed (j p) (j q) hp hq
    obtain ⟨s,_,rfl⟩ := (full B r).mp (h.proper r hr).1
    exact ⟨s,hr,(entry s p R).mpr rp,(entry s q R).mpr rq⟩
  · intro p hp D dense
    obtain ⟨E,inter⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) B D
    have hE := (power E).mpr (fun q hq => ((inter q).mp hq).1)
    have denseE : Dense_d M B R z (fun q => M.mem q E) p := fun q hq =>
      (dense q hq).imp fun r hr => ⟨hr.1,(inter r).mpr ⟨hr.1.1,hr.2⟩⟩
    obtain ⟨q,hq,qe⟩ := h.meets (j p) hp (j E) ((image_member_l j inj full).mpr hE)
      ((image_dense_set_l hZF hN j inj full).mpr denseE)
    obtain ⟨r,_,rfl⟩ := (full B q).mp (h.proper q hq).1
    exact ⟨r,hq,((inter r).mp ((image_member_l j inj full).mp qe)).2⟩

/-- 枚举旧全局稠密集也足以生成原泛型；局部要求由不相容部分补成全局要求。 -/
theorem Gset_d.ground_global_l {B R z 𝒟 : M.Domain} {H : N.Domain}
    (O : Cond_order_d M B R z)
    (cover : ∀ D, Dense_set_d M B R z D → M.mem D 𝒟)
    (h : Gset_d (j B) (j R) (j z) (j 𝒟) H) :
    Generic_d M B R z (fun p => N.mem (j p) H) := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hZF)) hN
  have proper p (hp : N.mem (j p) H) : M.mem p B ∧ p ≠ z :=
    ⟨(image_member_l j inj full).mp (h.proper (j p) hp).1,
      fun eq => (h.proper (j p) hp).2 (congrArg j eq)⟩
  have directed p q (hp : N.mem (j p) H) (hq : N.mem (j q) H) :
      ∃ r, N.mem (j r) H ∧ Entry_d M r p R ∧ Entry_d M r q R := by
    obtain ⟨r,hr,rp,rq⟩ := h.directed (j p) (j q) hp hq
    obtain ⟨s,_,rfl⟩ := (full B r).mp (h.proper r hr).1
    exact ⟨s,hr,(entry s p R).mpr rp,(entry s q R).mpr rq⟩
  refine ⟨proper,?_,?_,directed,?_⟩
  · obtain ⟨p,hp⟩ := h.inhabited
    obtain ⟨q,_,rfl⟩ := (full B p).mp (h.proper p hp).1
    exact ⟨q,hp⟩
  · intro p q hp hq pq
    exact h.upward (j p) (j q) hp ((image_member_l j inj full).mpr hq) ((entry p q R).mp pq)
  · intro p hp D dense
    obtain ⟨E,global,members⟩ := dense_globalize_l hZF O (proper p hp).1 dense
    obtain ⟨q,hq,qE⟩ := h.meets (j p) hp (j E) ((image_member_l j inj full).mpr (cover E global))
      ((image_dense_set_l hZF hN j inj full).mpr (fun r hr => global.2 r hr.1 hr.2.1))
    obtain ⟨r,_,rfl⟩ := (full B q).mp (h.proper q hq).1
    have accepted := ((members r).mp ((image_member_l j inj full).mp qE)).2.2
    refine ⟨r,hq,accepted.elim (fun no => ?_) And.right⟩
    obtain ⟨s,hs,sr,sp⟩ := directed r p hq hp
    exact (no ⟨s,⟨(proper s hs).1,(proper s hs).2,sr⟩,sp⟩).elim

end YesMetaZFC.Model.Forcing.Internal
