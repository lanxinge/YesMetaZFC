import YesMetaZFC.Model.Forcing.Boolean.GroundGeneric
import YesMetaZFC.Model.SetTheory.Internal.RealTrace
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.Model.Forcing.Collapse.ProductCoordinates
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative

/-! # 以原载体为稠密参数域的背景泛型公式

背景公式量化原模型载体 X 中的全部集合。传递性使条件以下的稠密性双向绝对，
故这一单一集合公式精确等价于原模型上的完整泛型性，无需背景幂集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hM : Extensional M)
  {c X R : M.Domain} (source : Smem_d I c X R) (trans : M.TransitiveSet X)
local notation "N" => smdl_structure_l I (R := R) (And.left (And.right (And.left source)))
include hM trans

/-- 原模型中的全局稠密集与其背景集合呈示等价；只需成员满性和配对。 -/
theorem Smem_d.dense_code_l (hN : (N).Models KP) (B T z D : (N).Domain) :
    Dense_set_d M B.val T.val z.val D.val ↔ Dense_set_d N B T z D := by
  have inj : Function.Injective (Subtype.val : (N).Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have member {a b : (N).Domain} : M.mem a.val b.val ↔ (N).mem a b :=
    @image_member_l N M Subtype.val inj full a b
  have edge := @image_entry_iff_l N M Subtype.val inj full (KP.exists_pair hN) hM
  have below (p q : (N).Domain) : Below_d N B T z p q ↔ Below_d M B.val T.val z.val p.val q.val :=
    and_congr member.symm (and_congr (not_congr inj.eq_iff.symm) (edge p q T))
  constructor
  · intro h
    refine ⟨fun p hp => ⟨member.mp (h.1 p.val (member.mpr hp)).1,
      fun eq => (h.1 p.val (member.mpr hp)).2 (congrArg Subtype.val eq)⟩,?_⟩
    intro p hp nz
    obtain ⟨q,qp,qD⟩ := h.2 p.val (member.mpr hp) (fun eq => nz (inj eq))
    obtain ⟨r,_,eq⟩ := (full B q).mp qp.1
    subst q
    exact ⟨r,(below r p).mpr qp,member.mp qD⟩
  · intro h
    constructor
    · intro p hp
      obtain ⟨q,hq,eq⟩ := (full D p).mp hp
      subst p
      exact ⟨member.mpr (h.1 q hq).1,fun eq => (h.1 q hq).2 (inj eq)⟩
    · intro p hp nz
      obtain ⟨q,hq,eq⟩ := (full B p).mp hp
      subst p
      obtain ⟨r,rq,rD⟩ := h.2 q hq (fun eq => nz (congrArg Subtype.val eq))
      exact ⟨r.val,(below r q).mp rq,member.mpr rD⟩

theorem Smem_d.generic_code_l (hN : (N).Models KP) (B T z : (N).Domain) (H : M.Domain) :
    Gset_d B.val T.val z.val X H ↔ M.MemberSubset H B.val ∧
      Generic_d N B T z (fun p => M.mem p.val H) := by
  have inj : Function.Injective (Subtype.val : (N).Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have member {a b : (N).Domain} : M.mem a.val b.val ↔ (N).mem a b :=
    @image_member_l N M Subtype.val inj full a b
  have edge := @image_entry_iff_l N M Subtype.val inj full (KP.exists_pair hN) hM
  have below (p q : (N).Domain) : Below_d N B T z p q ↔ Below_d M B.val T.val z.val p.val q.val :=
    and_congr member.symm (and_congr (not_congr inj.eq_iff.symm) (edge p q T))
  have density (D p : (N).Domain) : Dense_d N B T z (fun q => (N).mem q D) p ↔
      Dense_d M B.val T.val z.val (fun q => M.mem q D.val) p.val := by
    constructor
    · intro h q hq
      obtain ⟨q₀,_,eq⟩ := (full B q).mp hq.1
      subst q
      obtain ⟨s,sp,sD⟩ := h q₀ ((below q₀ p).mpr hq)
      exact ⟨s.val,(below s q₀).mp sp,member.mpr sD⟩
    · intro h q hq
      obtain ⟨s,sq,sD⟩ := h q.val ((below q p).mp hq)
      obtain ⟨s₀,_,eq⟩ := (full B s).mp sq.1
      subst s
      exact ⟨s₀,(below s₀ q).mpr sq,member.mp sD⟩
  constructor
  · intro h
    refine ⟨fun q hq => (h.proper q hq).1,?_,?_,?_,?_,?_⟩
    · intro p hp
      exact ⟨member.mp (h.proper p.val hp).1,fun eq => (h.proper p.val hp).2 (congrArg Subtype.val eq)⟩
    · obtain ⟨p,hp⟩ := h.inhabited
      obtain ⟨q,_,eq⟩ := (full B p).mp (h.proper p hp).1
      exact ⟨q,eq.symm ▸ hp⟩
    · intro p q hp hq pq
      exact h.upward p.val q.val hp (member.mpr hq) ((edge p q T).mp pq)
    · intro p q hp hq
      obtain ⟨s,hs,sp,sq⟩ := h.directed p.val q.val hp hq
      obtain ⟨r,_,eq⟩ := (full B s).mp (h.proper s hs).1
      subst s
      exact ⟨r,hs,(edge r p T).mpr sp,(edge r q T).mpr sq⟩
    · intro p hp D hd
      obtain ⟨q,hq,qD⟩ := h.meets p.val hp D.val D.property ((density D p).mp hd)
      obtain ⟨q₀,_,eq⟩ := (full B q).mp (h.proper q hq).1
      subst q
      exact ⟨q₀,hq,member.mp qD⟩
  · rintro ⟨sub,generic⟩
    have lift p (hp : M.mem p H) : ∃ q : (N).Domain, M.mem q.val H ∧ q.val = p := by
      obtain ⟨q,_,eq⟩ := (full B p).mp (sub p hp)
      exact ⟨q,eq.symm ▸ hp,eq⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro p hp
      obtain ⟨q,hq,rfl⟩ := lift p hp
      exact ⟨sub q.val hq,fun eq => (generic.proper q hq).2 (inj eq)⟩
    · obtain ⟨p,hp⟩ := generic.inhabited
      exact ⟨p.val,hp⟩
    · intro p q hp hq pq
      obtain ⟨p₀,hp,rfl⟩ := lift p hp
      obtain ⟨q₀,hq₀,eq⟩ := (full B q).mp hq
      subst q
      exact generic.upward p₀ q₀ hp hq₀ ((edge p₀ q₀ T).mpr pq)
    · intro p q hp hq
      obtain ⟨p₀,hp,rfl⟩ := lift p hp
      obtain ⟨q₀,hq,rfl⟩ := lift q hq
      obtain ⟨r,hr,rp,rq⟩ := generic.directed p₀ q₀ hp hq
      exact ⟨r.val,hr,(edge r p₀ T).mp rp,(edge r q₀ T).mp rq⟩
    · intro p hp D hD hd
      obtain ⟨p₀,hp,rfl⟩ := lift p hp
      let D₀ : (N).Domain := ⟨D,hD⟩
      obtain ⟨q,hq,qD⟩ := generic.meets p₀ hp D₀ ((density D₀ p₀).mpr hd)
      exact ⟨q.val,hq,member.mpr qD⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原模型全部稠密集族的背景编码与初等运输

成员满性使全局稠密性绝对。将完整族的规格送过原模型间的初等图后，
所得像覆盖目标模型的全部稠密集，而不仅是逐项搬运旧族成员。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

structure Df_family_d (X P T E : M.Domain) : Prop where
  inside : M.mem E X
  members : ∀ D, M.mem D E ↔ M.mem D X ∧ Dense_set_d M P T P D

def df_family_m {n} (X P T E : Term n) : Formula 1 n := set[n] ⟪
  ⌜E⌝ₛ ∈ ⌜X⌝ₛ ∧ (∀ D, D ∈ ⌜E⌝ₛ ↔ D ∈ ⌜X⌝ₛ ∧ ⌜dense_set_m⌝ₚ(⌜P⌝ₛ,⌜T⌝ₛ,⌜P⌝ₛ,D))⟫
derive_free_closed df_family_m

theorem df_family_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X P T E : Term n) :
    Formula.satisfies ρ (df_family_m X P T E) ↔ Df_family_d (X.eval ρ) (P.eval ρ) (T.eval ρ) (E.eval ρ) := by
  simp only [df_family_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,dense_set_sat_l M hE,Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.inside,h.members⟩⟩

variable (I : kpair_convention_l.Interpretation M)

theorem df_family_read_l (hM : Extensional M) {c X R : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models KP)
    (P T E : (smdl_structure_l I (R := R) source.1.2.1).Domain) :
    Df_family_d X P.val T.val E.val ↔
      ∀ D, (smdl_structure_l I (R := R) source.1.2.1).mem D E ↔
        Dense_set_d (smdl_structure_l I (R := R) source.1.2.1) P T P D := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  constructor
  · intro h D
    exact ⟨fun hd => (source.dense_code_l I hM trans native P T P D).mp
      ((h.members D.val).mp ((source.2 D.val E.val).mp hd).2.2).2,
      fun hd => (source.2 D.val E.val).mpr ⟨D.property,E.property,
        (h.members D.val).mpr ⟨D.property,(source.dense_code_l I hM trans native P T P D).mpr hd⟩⟩⟩
  · intro h
    refine ⟨E.property,fun D => ?_⟩
    constructor
    · intro hd
      have inside := trans E.val E.property D hd
      let D₀ : N.Domain := ⟨D,inside⟩
      exact ⟨inside,(source.dense_code_l I hM trans native P T P D₀).mpr
        ((h D₀).mp ((source.2 D E.val).mpr ⟨inside,E.property,hd⟩))⟩
    · rintro ⟨inside,dense⟩
      let D₀ : N.Domain := ⟨D,inside⟩
      exact ((source.2 D E.val).mp ((h D₀).mpr
        ((source.dense_code_l I hM trans native P T P D₀).mp dense))).2.2

/-- 运输完整族的原公式，因此目标中新出现的稠密集也属于同一个族的像。 -/
theorem Df_family_d.image_l (hZF : M.Models ZF) {Ω c X R c' X' R' j : M.Domain}
    (hΩ : M.IsOmega Ω) (source : Smem_d I c X R) (target : Smem_d I c' X' R')
    (xt : M.TransitiveSet X) (yt : M.TransitiveSet X') (map : Smap_d I Ω c c' X X' j)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models KP)
    (native' : (smdl_structure_l I (R := R') target.1.2.1).Models KP)
    {P T E : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {P' T' : (smdl_structure_l I (R := R') target.1.2.1).Domain}
    (h : Df_family_d X P.val T.val E.val) (pP : M.PairMember I P.val P'.val j) (tT : M.PairMember I T.val T'.val j) :
    ∃ E', Df_family_d X' P'.val T'.val E' ∧ M.PairMember I E.val E' j := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let N' := smdl_structure_l I (R := R') target.1.2.1
  obtain ⟨E',hE',eE⟩ := map.1.1.2.2 E.val E.property
  let E₀ : N'.Domain := ⟨E',hE'⟩
  let φ : Formula 1 3 := .forallE (.iff (.mem .newest (.bound 3))
    (dense_set_m (.bound 1) (.bound 2) (.bound 1) .newest))
  let ρ : Env N 3 := ⟨fun i => [P,T,E].get i,fun _ => P⟩
  let η : Env N' 3 := ⟨fun i => [P',T',E₀].get i,fun _ => P'⟩
  have sourceRead : Formula.satisfies ρ φ ↔ ∀ D, N.mem D E ↔ Dense_set_d N P T P D := by
    simp only [φ,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,dense_set_sat_l N native.1]
    rfl
  have targetRead : Formula.satisfies η φ ↔ ∀ D, N'.mem D E₀ ↔ Dense_set_d N' P' T' P' D := by
    simp only [φ,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,dense_set_sat_l N' native'.1]
    rfl
  have moved := smap_source_l I hZF hΩ source.1 target.1 map φ
    (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed,dense_set_m_freeClosed]) ρ η
    (Fin.cases pP (Fin.cases tT (Fin.cases eE (fun i => Fin.elim0 i))))
  exact ⟨E',(df_family_read_l I hZF.1 target yt native' P' T' E₀).mpr
    (targetRead.mp (moved.mp (sourceRead.mpr ((df_family_read_l I hZF.1 source xt native P T E).mp h)))),eE⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原模型参数域的背景泛型性向外保持

稠密参数仍遍历原载体的全部成员。成员满嵌入回收每个条件和稠密参数，
从而运输同一个已集合化的滤子，无须外层幂集等于旧幂集。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem Gset_d.image_l (hM : M.Models ZF) (hN : Extensional N)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
    {B R z X H : M.Domain} (g : Gset_d B R z X H) : Gset_d (e B) (e R) (e z) (e X) (e H) := by
  have mem {a b : M.Domain} := image_member_l e inj full (a := a) (b := b)
  have entry := image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hM)) hN
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨a,ha,rfl⟩ := (full H p).mp hp
    exact ⟨mem.mpr (g.proper a ha).1,fun eq => (g.proper a ha).2 (inj eq)⟩
  · obtain ⟨a,ha⟩ := g.inhabited
    exact ⟨e a,mem.mpr ha⟩
  · intro p q hp hq pq
    obtain ⟨a,ha,rfl⟩ := (full H p).mp hp
    obtain ⟨b,hb,rfl⟩ := (full B q).mp hq
    exact mem.mpr (g.upward a b ha hb ((entry a b R).mpr pq))
  · intro p q hp hq
    obtain ⟨a,ha,rfl⟩ := (full H p).mp hp
    obtain ⟨b,hb,rfl⟩ := (full H q).mp hq
    obtain ⟨c,hc,ca,cb⟩ := g.directed a b ha hb
    exact ⟨e c,mem.mpr hc,(entry c a R).mp ca,(entry c b R).mp cb⟩
  · intro p hp D hD dense
    obtain ⟨a,ha,rfl⟩ := (full H p).mp hp
    obtain ⟨E,hE,rfl⟩ := (full X D).mp hD
    obtain ⟨b,hb,bE⟩ := g.meets a ha E hE ((image_dense_set_l hM hN e inj full).mp dense)
    exact ⟨e b,mem.mpr hb,mem.mpr bE⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 实际背景泛型集合的有限前缀投影

原全乘积顺序直接定义投影集合，不选取商滤子或新的泛型。
同一集合方程同时适用于全乘积泛型和较长有限前缀泛型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}}

def Fp_filter_project_d (C T H K : M.Domain) : Prop := ∀ q, M.mem q K ↔
  M.mem q C ∧ ∃ p, M.mem p H ∧ Entry_d M p q T

/-- 投影由条件域内的有界分离确定；此矩阵可直接沿反坍塌反射。 -/
def fp_filter_project_m {n} (C T H K : Term n) : Formula 1 n :=
  .conj (Formula.subset K C) (Formula.forallMem C
    (.iff (.mem .newest K.weaken) (Formula.existsMem H.weaken
      (rd_entry0_m .newest (.bound 1) T.weaken.weaken))))
derive_free_closed fp_filter_project_m

theorem fp_filter_project_delta_l {n} (C T H K : Term n) : (fp_filter_project_m C T H K).IsDelta0 :=
  .conj (.atom ..) (.forallMem _ (.iff (.mem ..) (.existsMem _ (rd_entry0_delta_l ..))))

theorem fp_filter_project_sat_l (hE : Extensional M) {n} (ρ : Env M n) (C T H K : Term n) :
    Formula.satisfies ρ (fp_filter_project_m C T H K) ↔
      Fp_filter_project_d (C.eval ρ) (T.eval ρ) (H.eval ρ) (K.eval ρ) := by
  simp only [fp_filter_project_m,Formula.satisfies_conj_iff,Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff,rd_entry0_sat_l hE,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨sub,rule⟩ q
    exact ⟨fun hq => ⟨sub q hq,(rule q (sub q hq)).mp hq⟩,
      fun ⟨hq,hit⟩ => (rule q hq).mpr hit⟩
  · intro h
    exact ⟨fun q hq => ((h q).mp hq).1,fun q hq => ⟨fun hk => ((h q).mp hk).2,
      fun hit => (h q).mpr ⟨hq,hit⟩⟩⟩

theorem fp_filter_project_l (hKP : M.Models KP) (C T H : M.Domain) : ∃ K, Fp_filter_project_d C T H K := by
  let ρ : Env M 2 := ⟨fun k => [H,T].get k,fun _ => H⟩
  let φ : Delta0UnarySchema 2 := {
    body := Formula.existsMem (.bound 1) (rd_entry0_m .newest (.bound 1) (.bound 3))
    delta0 := .existsMem _ (rd_entry0_delta_l ..) }
  obtain ⟨K,sep⟩ := KP.separation_exists_d hKP φ ρ C
  refine ⟨K,fun q => (sep q).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ,Formula.satisfies_existsMem_iff,rd_entry0_sat_l hKP.1]
  rfl

theorem Fp_filter_project_d.unique_l (hM : Extensional M) {C T H K L : M.Domain}
    (h : Fp_filter_project_d C T H K) (k : Fp_filter_project_d C T H L) : K = L :=
  hM.eq_of_same_members K L (fun q => (h q).trans (k q).symm)

theorem Fp_filter_project_d.image_l {N : Structure} (hM : M.Models KP) (hN : Extensional N)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
    {C T H K : M.Domain} (h : Fp_filter_project_d C T H K) :
    Fp_filter_project_d (e C) (e T) (e H) (e K) := by
  intro q
  constructor
  · intro hq
    obtain ⟨q₀,hq₀,rfl⟩ := (full K q).mp hq
    obtain ⟨qc,p,hp,pq⟩ := (h q₀).mp hq₀
    exact ⟨(image_member_l e inj full).mpr qc,e p,(image_member_l e inj full).mpr hp,
      (image_entry_iff_l e inj full (KP.exists_pair hM) hN p q₀ T).mp pq⟩
  · rintro ⟨hq,p,hp,pq⟩
    obtain ⟨q₀,hq₀,rfl⟩ := (full C q).mp hq
    obtain ⟨p₀,hp₀,rfl⟩ := (full H p).mp hp
    exact (image_member_l e inj full).mpr ((h q₀).mpr ⟨hq₀,p₀,hp₀,
      (image_entry_iff_l e inj full (KP.exists_pair hM) hN p₀ q₀ T).mpr pq⟩)

variable (hM : M.Models ZF) {c X R : M.Domain}
  (source : Smem_d (kp_pair_l (ZF.modelsKP hM)) c X R) (trans : M.TransitiveSet X)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1).Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
include trans native

theorem Smem_d.project_filter_read_l
    {ω A n C S P T : (smdl_structure_l I (R := R) source.1.2.1).Domain} {H K : M.Domain}
    (product : Fp_product_d native ω A P T) (stage : Fp_prefix_d native ω A n C S)
    (hn : (smdl_structure_l I (R := R) source.1.2.1).mem n ω)
    (sub : M.MemberSubset H P.val) (projection : Fp_filter_project_d C.val T.val H K) :
    ∀ q : (smdl_structure_l I (R := R) source.1.2.1).Domain,
      M.mem q.val K ↔ Fp_project_d (kp_pair_l (ZF.modelsKP native)) C (fun p => M.mem p.val H) q := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have mem {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b := image_member_l (M := N) (N := M) Subtype.val inj full
  have entry := image_entry_iff_l (M := N) (N := M) Subtype.val inj full (KP.exists_pair (ZF.modelsKP native)) hM.1
  intro q
  apply (projection q.val).trans
  constructor
  · rintro ⟨hq,p,hp,pq⟩
    let p₀ : N.Domain := ⟨p,trans P.val P.property p (sub p hp)⟩
    exact ⟨mem.mp hq,p₀,hp,((product.order p₀ q).mp ((entry p₀ q T).mpr pq)).2.2⟩
  · rintro ⟨hq,p,hp,le⟩
    exact ⟨mem.mpr hq,p.val,hp,(entry p q T).mp ((product.order p q).mpr
      ⟨mem.mp (sub p.val hp),((stage.product_read_l native product hn).1 q).mp hq |>.1,le⟩)⟩

theorem Smem_d.product_project_l
    {ω A n C S P T W : (smdl_structure_l I (R := R) source.1.2.1).Domain} {H : M.Domain}
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (hn : (smdl_structure_l I (R := R) source.1.2.1).mem n ω)
    (fa : (smdl_structure_l I (R := R) source.1.2.1).IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) A ω W)
    (product : Fp_product_d native ω A P T) (stage : Fp_prefix_d native ω A n C S)
    (generic : Gset_d P.val T.val P.val X H) :
    ∃ K, Fp_filter_project_d C.val T.val H K ∧ Gset_d C.val S.val C.val X K := by
  obtain ⟨sub,g⟩ := (source.generic_code_l I hM.1 trans (ZF.modelsKP native) P T P H).mp generic
  have small := product.project_generic_l native hw hn fa stage g
  obtain ⟨K,projection⟩ := fp_filter_project_l (ZF.modelsKP hM) C.val T.val H
  have read := Smem_d.project_filter_read_l hM source trans native product stage hn sub projection
  have same : (fun q => M.mem q.val K) = Fp_project_d (kp_pair_l (ZF.modelsKP native)) C (fun p => M.mem p.val H) :=
    funext (fun q => propext (read q))
  exact ⟨K,projection,(source.generic_code_l I hM.1 trans (ZF.modelsKP native) C S C K).mpr
    ⟨fun q hq => ((projection q).mp hq).1,same.symm ▸ small⟩⟩

theorem Smem_d.prefix_project_l
    {ω A n m C S D V P T : (smdl_structure_l I (R := R) source.1.2.1).Domain} {H : M.Domain}
    (hn : (smdl_structure_l I (R := R) source.1.2.1).mem n ω)
    (hm : (smdl_structure_l I (R := R) source.1.2.1).mem m ω)
    (sub : (smdl_structure_l I (R := R) source.1.2.1).MemberSubset n m)
    (product : Fp_product_d native ω A P T)
    (small : Fp_prefix_d native ω A n C S) (large : Fp_prefix_d native ω A m D V)
    (generic : Gset_d D.val V.val D.val X H) :
    ∃ K, Fp_filter_project_d C.val T.val H K ∧ Gset_d C.val S.val C.val X K := by
  obtain ⟨hD,g⟩ := (source.generic_code_l I hM.1 trans (ZF.modelsKP native) D V D H).mp generic
  have gp := small.project_generic_l native large sub g
  have hP : M.MemberSubset H P.val := by
    intro p hp
    let p₀ : (smdl_structure_l I (R := R) source.1.2.1).Domain := ⟨p,trans D.val D.property p (hD p hp)⟩
    have pp := ((large.product_read_l native product hm).1 p₀).mp
      ((source.2 p D.val).mpr ⟨p₀.property,D.property,hD p hp⟩)
    exact ((source.2 p P.val).mp pp.1).2.2
  obtain ⟨K,projection⟩ := fp_filter_project_l (ZF.modelsKP hM) C.val T.val H
  have read := Smem_d.project_filter_read_l hM source trans native product small hn hP projection
  have same : (fun q => M.mem q.val K) = Fp_project_d (kp_pair_l (ZF.modelsKP native)) C (fun p => M.mem p.val H) :=
    funext (fun q => propext (read q))
  exact ⟨K,projection,(source.generic_code_l I hM.1 trans (ZF.modelsKP native) C S C K).mpr
    ⟨fun q hq => ((projection q).mp hq).1,same.symm ▸ gp⟩⟩

end YesMetaZFC.Model.Forcing.Internal
