import YesMetaZFC.Model.Forcing.Collapse.ProductCoordinates
import YesMetaZFC.Model.Forcing.Embedding.Rank
import YesMetaZFC.Model.Forcing.Automorphism.RealSetName
import YesMetaZFC.Model.Forcing.Functions.ValueIsomorphism
import YesMetaZFC.Model.Forcing.Stage.Extension
import YesMetaZFC.Model.Forcing.Stage.NameMap.Support
import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.Forcing.Names.CheckPools
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.SetTheory.Images.BinaryImage
import YesMetaZFC.Model.Forcing.Ground.ProductProjection
import YesMetaZFC.Model.Forcing.Ground.RealCodeImage
import YesMetaZFC.Model.Forcing.Ground.RealValue
import YesMetaZFC.Model.Forcing.Ground.BackgroundExtension
import YesMetaZFC.Model.Forcing.Ground.RealGround

/-! # 全乘积及稠密任务沿实际初等嵌入运输

条件空间和顺序都用原对象公式表达；运输后的断言量化目标模型的全部条件及集合。
有限任务保留原指定坐标块，稠密性也在目标全乘积中成立。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v

def fp_product_m {d} (ω A P R : Term d) : Formula 1 d := set[d] ⟪
  (∀ p, p ∈ ⌜P⌝ₛ ↔ ∃ n ∈ ⌜ω⌝ₛ, ⌜fp_at_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,n,p)) ∧
    (∀ p q, ⌜entry_m⌝ₚ(p,q,⌜R⌝ₛ) ↔ p ∈ ⌜P⌝ₛ ∧ q ∈ ⌜P⌝ₛ ∧
      ⌜fp_le_m (𝒞 := kpair_convention_l)⌝ₚ(p,q))⟫
derive_free_closed fp_product_m

def fp_prefix_m {d} (ω A n C S : Term d) : Formula 1 d := set[d] ⟪
  (∀ p, p ∈ ⌜C⌝ₛ ↔ ⌜fp_at_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜n⌝ₛ,p)) ∧
    (∀ p q, ⌜entry_m⌝ₚ(p,q,⌜S⌝ₛ) ↔ p ∈ ⌜C⌝ₛ ∧ q ∈ ⌜C⌝ₛ ∧
      ⌜fp_le_m (𝒞 := kpair_convention_l)⌝ₚ(p,q))⟫
derive_free_closed fp_prefix_m

theorem fp_prefix_sat_l {M : Structure.{u}} (hM : M.Models ZF) {d} (ρ : Env M d) (ω A n C S : Term d) :
    Formula.satisfies ρ (fp_prefix_m ω A n C S) ↔
      Fp_prefix_d hM (ω.eval ρ) (A.eval ρ) (n.eval ρ) (C.eval ρ) (S.eval ρ) := by
  let I := kpair_interpretation_l M hM.1 (KP.exists_pair (ZF.modelsKP hM))
  simp only [fp_prefix_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,fp_at_sat_l I hM.1,fp_le_sat_l I,
    entry_sat_l M hM.1,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨s,r⟩ => ⟨s,r⟩,fun h => ⟨h.conditions,h.order⟩⟩

theorem fp_product_sat_l {M : Structure.{u}} (hM : M.Models ZF) {d} (ρ : Env M d) (ω A P R : Term d) :
    Formula.satisfies ρ (fp_product_m ω A P R) ↔ Fp_product_d hM (ω.eval ρ) (A.eval ρ) (P.eval ρ) (R.eval ρ) := by
  let I := kpair_interpretation_l M hM.1 (KP.exists_pair (ZF.modelsKP hM))
  simp only [fp_product_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,Formula.satisfies_existsMem_iff,
    fp_at_sat_l I hM.1,fp_le_sat_l I,entry_sat_l M hM.1,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨s,r⟩ => ⟨s,r⟩,fun h => ⟨h.conditions,h.order⟩⟩

variable {N : Structure.{u}} {M : Structure.{v}} (hN : N.Models ZF) (hM : M.Models ZF)
  (e : N.Domain → M.Domain) (elem : Pe_d e)
local notation "I" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
local notation "J" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
include elem

theorem fp_at_image_l {ω A n p : N.Domain} (h : Fp_at_d I ω A n p) :
    Fp_at_d J (e ω) (e A) (e n) (e p) := by
  let ρ : Env N 4 := ⟨fun i => [ω,A,n,p].get i,fun _ => p⟩
  let φ := fp_at_m (𝒞 := kpair_convention_l) (.bound 0 : Term 4) (.bound 1) (.bound 2) (.bound 3)
  exact (fp_at_sat_l J hM.1 (image_env_l e ρ) _ _ _ _).mp
    ((elem φ (by simp -implicitDefEqProofs [φ]) ρ).mp ((fp_at_sat_l I hN.1 ρ _ _ _ _).mpr h))

theorem fp_prefix_image_l {ω A n C S : N.Domain} (h : Fp_prefix_d hN ω A n C S) :
    Fp_prefix_d hM (e ω) (e A) (e n) (e C) (e S) := by
  let ρ : Env N 5 := ⟨fun i => [ω,A,n,C,S].get i,fun _ => S⟩
  let φ := fp_prefix_m (.bound 0 : Term 5) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
  exact (fp_prefix_sat_l hM (image_env_l e ρ) _ _ _ _ _).mp
    ((elem φ (by simp -implicitDefEqProofs [φ]) ρ).mp ((fp_prefix_sat_l hN ρ _ _ _ _ _).mpr h))

theorem fp_product_image_l {ω A P R : N.Domain} (h : Fp_product_d hN ω A P R) :
    Fp_product_d hM (e ω) (e A) (e P) (e R) := by
  let ρ : Env N 4 := ⟨fun i => [ω,A,P,R].get i,fun _ => P⟩
  let φ := fp_product_m (.bound 0 : Term 4) (.bound 1) (.bound 2) (.bound 3)
  exact (fp_product_sat_l hM (image_env_l e ρ) _ _ _ _).mp
    ((elem φ (by simp -implicitDefEqProofs [φ]) ρ).mp ((fp_product_sat_l hN ρ _ _ _ _).mpr h))

theorem fp_dense_image_l (hEN : Extensional N) (hEM : Extensional M) {P R D : N.Domain}
    (dense : Dense_set_d N P R P D) :
    Dense_set_d M (e P) (e R) (e P) (e D) := by
  let ρ : Env N 3 := ⟨fun i => [P,R,D].get i,fun _ => P⟩
  let φ := dense_set_m (.bound 0 : Term 3) (.bound 1) (.bound 0) (.bound 2)
  exact (dense_set_sat_l M hEM (image_env_l e ρ) _ _ _ _).mp
    ((elem φ (by simp -implicitDefEqProofs [φ,dense_set_m_freeClosed]) ρ).mp
      ((dense_set_sat_l N hEN ρ _ _ _ _).mpr dense))

end YesMetaZFC.Model.Forcing.Internal

/-! ## 唯一的有限前缀及其最大条件

顺序同时保存实际关系性，以排除非有序对杂项。条件域、关系和最大条件
均由 ω、字母表及长度唯一决定，可直接用于内部替代。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fp_le_antisymm_l (J : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {p q : M.Domain} (fp : M.IsSetFunction J p) (fq : M.IsSetFunction J q)
    (pq : Fp_le_d J p q) (qp : Fp_le_d J q p) : p = q := by
  have entries {p q} (fp : M.IsSetFunction J p) (pq : Fp_le_d J p q) (qp : Fp_le_d J q p)
      {i s} (edge : M.PairMember J i s p) : M.PairMember J i s q := by
    obtain ⟨t,it,st⟩ := qp i s edge
    obtain ⟨u,iu,tu⟩ := pq i t it
    have eq := fp.2 i u s iu edge
    have same : s = t := hE.eq_of_same_members s t (fun v => ⟨st v,fun hv => eq ▸ tu v hv⟩)
    exact same.symm ▸ it
  exact fp.1.eq_of_pairMember_iff hE fq.1 (fun i s => ⟨entries fp pq qp,entries fq qp pq⟩)

structure Fp_stage_d (ω A n C S b : M.Domain) : Prop where
  stage : Fp_prefix_d hZF ω A n C S
  relation : M.IsSetRelation I S
  member : M.mem b C
  top : ∀ p, M.mem p C → Entry_d M p b S

theorem Fp_product_d.stage_l {ω A P R n U : M.Domain} (product : Fp_product_d hZF ω A P R)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (fa : M.IsSetFunctionFromTo I A ω U) :
    ∃ C S b, Fp_stage_d hZF ω A n C S b := by
  obtain ⟨C,T,stage⟩ := product.prefix_l hZF hn
  let ρ : Env M 0 := ⟨Fin.elim0,fun _ => n⟩
  let φ : BinarySchema 0 := { body := fp_le_m (𝒞 := kpair_convention_l) (.bound 1) .newest }
  obtain ⟨S,rel,entries⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ C
  have new : Fp_prefix_d hZF ω A n C S := ⟨stage.conditions,fun p q => (entries p q).trans
    (and_congr_right fun _ => and_congr_right fun _ => fp_le_sat_l I ..)⟩
  obtain ⟨b,hb,top⟩ := new.top_l hZF hw hn fa
  exact ⟨C,S,b,new,rel.1,hb,top⟩

theorem Fp_stage_d.unique_l {ω A n C S b D T d : M.Domain}
    (h : Fp_stage_d hZF ω A n C S b) (k : Fp_stage_d hZF ω A n D T d) : C = D ∧ S = T ∧ b = d := by
  have ec := hZF.1.eq_of_same_members C D (fun p => (h.stage.conditions p).trans (k.stage.conditions p).symm)
  subst D
  have es := h.relation.eq_of_pairMember_iff hZF.1 k.relation (fun p q => (h.stage.order p q).trans (k.stage.order p q).symm)
  subst T
  exact ⟨rfl,rfl,fp_le_antisymm_l I hZF.1 ((h.stage.conditions b).mp h.member).function
    ((k.stage.conditions d).mp k.member).function ((h.stage.order b d).mp (k.top b h.member)).2.2
    ((h.stage.order d b).mp (h.top d k.member)).2.2⟩

def fp_stage_m {d} (ω A n C S b : Term d) : Formula 1 d := set[d] ⟪
  ⌜fp_prefix_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜n⌝ₛ,⌜C⌝ₛ,⌜S⌝ₛ) ∧ ⌜Formula.isRelation kpair_convention_l⌝ₚ(⌜S⌝ₛ) ∧
  ⌜b⌝ₛ ∈ ⌜C⌝ₛ ∧ (∀ p ∈ ⌜C⌝ₛ, ⌜entry_m⌝ₚ(p,⌜b⌝ₛ,⌜S⌝ₛ))⟫
derive_free_closed fp_stage_m

theorem fp_stage_sat_l {d} (ρ : Env M d) (ω A n C S b : Term d) :
    Formula.satisfies ρ (fp_stage_m ω A n C S b) ↔
      Fp_stage_d hZF (ω.eval ρ) (A.eval ρ) (n.eval ρ) (C.eval ρ) (S.eval ρ) (b.eval ρ) := by
  simp only [fp_stage_m,Formula.satisfies_conj_iff,fp_prefix_sat_l hZF,Formula.satisfies_isRelation_iff I,
    Formula.satisfies_mem_iff,Formula.satisfies_forallMem_iff,entry_sat_l M hZF.1,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d⟩ => ⟨a,b,c,d⟩,fun h => ⟨h.stage,h.relation,h.member,h.top⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 保持长度的全乘积作用在每个有限前缀上的真实限制

限制图是原模型集合；最大条件由偏序反对称性固定。名字作用的限制由
恒等图与复合律证明，因而同一全乘积作用固定各前缀的规范实数名字。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Fp_aut_d (P R F : M.Domain) : Prop where
  aut : Aut_d M P R P F
  lengths : ∀ n p q, Entry_d M p q F → (M.IsDomainOf I n p ↔ M.IsDomainOf I n q)

def Fp_tail_d (n P R F : M.Domain) : Prop := Fp_aut_d I P R F ∧
  ∀ p q, Entry_d M p q F → ∀ i, M.mem i n → ∀ s, Entry_d M i s p ↔ Entry_d M i s q

variable (hZF : M.Models ZF)
local notation "J" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
include hZF

theorem nmap_restriction_l {C F G s t : M.Domain}
    (entries : ∀ p q, Entry_d M p q G ↔ M.mem p C ∧ Entry_d M p q F) (ns : Name_d M C s) :
    Nmap_d M F s t ↔ Nmap_d M G s t := by
  obtain ⟨K,_,id⟩ := aut_id_l hZF C C C
  have comp p q : Entry_d M p q G ↔ ∃ a, Entry_d M p a K ∧ Entry_d M a q F := by
    rw [entries]
    exact ⟨fun ⟨hp,pq⟩ => ⟨p,(id p p).mpr ⟨hp,rfl⟩,pq⟩,
      fun ⟨a,pa,aq⟩ => ⟨((id p a).mp pa).1,((id p a).mp pa).2 ▸ aq⟩⟩
  have forward := fun {u} (su : Nmap_d M F s u) => nmap_comp_l hZF comp (nmap_identity_l hZF id ns) su
  refine ⟨forward,fun st => ?_⟩
  obtain ⟨u,su⟩ := nmap_exists_l M hZF F s
  exact nmap_unique_l M hZF.1 (check_ind_l M hZF) G s u t (forward su) st ▸ su

theorem Fp_aut_d.restrict_l {ω A P R F n C S b : M.Domain}
    (product : Fp_product_d hZF ω A P R) (stage : Fp_stage_d hZF ω A n C S b)
    (hn : M.mem n ω) (h : Fp_aut_d J P R F) :
    ∃ G, Aut_d M C S C G ∧ Entry_d M b b G ∧
      (∀ p q, Entry_d M p q G ↔ M.mem p C ∧ Entry_d M p q F) ∧
      ∀ s t, Name_d M C s → (Nmap_d M F s t ↔ Nmap_d M G s t) := by
  have section₀ := stage.stage.product_read_l hZF product hn
  have preserve {p q} (pq : Entry_d M p q F) : M.mem p C ↔ M.mem q C :=
    (section₀.1 p).trans ((and_congr ⟨fun _ => (h.aut.domain p q pq).2,fun _ => (h.aut.domain p q pq).1⟩
      (h.lengths n p q pq)).trans (section₀.1 q).symm)
  let ρ : Env M 1 := ⟨fun _ => F,fun _ => F⟩
  let φ : BinarySchema 1 := { body := entry_m (.bound 1) .newest (.bound 2) }
  obtain ⟨G,rel,graph⟩ := ZF.exists_setRelationOn_of_denote hZF J φ ρ C
  have edges p q : Entry_d M p q G ↔ M.mem p C ∧ Entry_d M p q F := by
    apply (graph p q).trans
    have sat : φ.denote ρ p q ↔ Entry_d M p q F := entry_sat_l M hZF.1 ..
    rw [sat]
    exact ⟨fun ⟨hp,_,pq⟩ => ⟨hp,pq⟩,fun ⟨hp,pq⟩ => ⟨hp,(preserve pq).mp hp,pq⟩⟩
  have aut : Aut_d M C S C G := by
    refine ⟨rel.1,fun p q pq => ⟨((edges p q).mp pq).1,(preserve ((edges p q).mp pq).2).mp ((edges p q).mp pq).1⟩,
      ?_,?_,?_,?_,?_,?_⟩
    · intro p hp
      obtain ⟨q,pq⟩ := h.aut.total p ((section₀.1 p).mp hp).1
      exact ⟨q,(edges p q).mpr ⟨hp,pq⟩⟩
    · intro q hq
      obtain ⟨p,pq⟩ := h.aut.onto q ((section₀.1 q).mp hq).1
      exact ⟨p,(edges p q).mpr ⟨(preserve pq).mpr hq,pq⟩⟩
    · intro p q r pq pr
      exact h.aut.functional p q r ((edges p q).mp pq).2 ((edges p r).mp pr).2
    · intro p q r pr qr
      exact h.aut.injective p q r ((edges p r).mp pr).2 ((edges q r).mp qr).2
    · intro p q s t ps qt
      obtain ⟨hp,ps⟩ := (edges p s).mp ps
      obtain ⟨hq,qt⟩ := (edges q t).mp qt
      rw [section₀.2 p q,section₀.2 s t]
      exact and_congr (iff_of_true hp ((preserve ps).mp hp))
        (and_congr (iff_of_true hq ((preserve qt).mp hq)) (h.aut.order p q s t ps qt))
    · intro p q pq
      obtain ⟨hp,pq⟩ := (edges p q).mp pq
      exact iff_of_false (fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ hp))
        (fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ (preserve pq).mp hp))
  obtain ⟨b',bb'⟩ := aut.total b stage.member
  have top p (hp : M.mem p C) : Entry_d M p b' S := by
    obtain ⟨q,qp⟩ := aut.onto p hp
    exact (aut.order q b p b' qp bb').mp (stage.top q (aut.domain q p qp).1)
  have hb' := (aut.domain b b' bb').2
  have eq := fp_le_antisymm_l J hZF.1 ((stage.stage.conditions b').mp hb').function
    ((stage.stage.conditions b).mp stage.member).function
    ((stage.stage.order b' b).mp (stage.top b' hb')).2.2 ((stage.stage.order b b').mp (top b stage.member)).2.2
  exact ⟨G,aut,eq ▸ bb',edges,fun s t ns => nmap_restriction_l hZF edges ns⟩

theorem Fp_aut_d.real_name_fixed_l {ω A P R F n C S b r : M.Domain}
    (product : Fp_product_d hZF ω A P R) (stage : Fp_stage_d hZF ω A n C S b)
    (hn : M.mem n ω) (h : Fp_aut_d J P R F) (name : Rn_d J C S b ω r) : Nmap_d M F r r := by
  obtain ⟨G,aut,fixed,_,restrict⟩ := h.restrict_l hZF product stage hn
  obtain ⟨D,t,W,data⟩ := name
  exact (restrict r r data.name).mpr (data.aut_fixed_l hZF aut fixed)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 全部有限前缀实数并的规范名字及其尾部不变性

每个内部自然数的条件域、顺序、最大条件和实数名字均唯一，原模型替代
收集整族并取并。不变性量化所有保持长度的实际乘积自同构。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

def Rp_part_d (ω A n r : M.Domain) : Prop := ∃ C S b, Fp_stage_d hZF ω A n C S b ∧ Rn_d I C S b ω r

def rp_part_m {d} (ω A n r : Term d) : Formula 1 d := set[d] ⟪∃ C S b,
  ⌜fp_stage_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜n⌝ₛ,C,S,b) ∧ ⌜rn_m⌝ₚ(C,S,b,⌜ω⌝ₛ,⌜r⌝ₛ)⟫
derive_free_closed rp_part_m

theorem rp_part_sat_l {d} (ρ : Env M d) (ω A n r : Term d) :
    Formula.satisfies ρ (rp_part_m ω A n r) ↔ Rp_part_d hZF (ω.eval ρ) (A.eval ρ) (n.eval ρ) (r.eval ρ) := by
  simp only [rp_part_m,Rp_part_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    fp_stage_sat_l hZF,rn_sat_l I hZF.1,Definitional.Term.eval_weaken]
  rfl

theorem Rp_part_d.unique_l {ω A n r s : M.Domain} (h : Rp_part_d hZF ω A n r) (k : Rp_part_d hZF ω A n s) : r = s := by
  obtain ⟨C,S,b,stage,name⟩ := h
  obtain ⟨D,T,d,stage',name'⟩ := k
  obtain ⟨ec,es,eb⟩ := stage.unique_l hZF stage'
  subst D T d
  exact name.unique_l I hZF name'

structure Rp_name_d (ω A P r : M.Domain) : Prop where
  name : Name_d M P r
  members : ∀ v, M.mem v r ↔ ∃ n s, M.mem n ω ∧ Rp_part_d hZF ω A n s ∧ M.mem v s

def rp_name_m {d} (ω A P r : Term d) : Formula 1 d := set[d] ⟪
  ⌜name_m⌝ₚ(⌜P⌝ₛ,⌜r⌝ₛ) ∧ (∀ v, v ∈ ⌜r⌝ₛ ↔ ∃ n s,
    n ∈ ⌜ω⌝ₛ ∧ ⌜rp_part_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,n,s) ∧ v ∈ s)⟫
derive_free_closed rp_name_m

theorem rp_name_sat_l {d} (ρ : Env M d) (ω A P r : Term d) :
    Formula.satisfies ρ (rp_name_m ω A P r) ↔
      Rp_name_d hZF (ω.eval ρ) (A.eval ρ) (P.eval ρ) (r.eval ρ) := by
  simp only [rp_name_m,Formula.satisfies_conj_iff,name_sat_l M hZF.1,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_exists_iff,Formula.satisfies_mem_iff,rp_part_sat_l hZF,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b⟩ => ⟨a,b⟩,fun h => ⟨h.name,h.members⟩⟩

theorem Rp_name_d.unique_l {ω A P r s : M.Domain} (h : Rp_name_d hZF ω A P r) (k : Rp_name_d hZF ω A P s) : r = s :=
  hZF.1.eq_of_same_members r s (fun v => (h.members v).trans (k.members v).symm)

theorem name_conditions_mono_l {C P t : M.Domain} (sub : M.MemberSubset C P) (nt : Name_d M C t) : Name_d M P t := by
  obtain ⟨S,ht,supp⟩ := nt
  refine ⟨S,ht,fun s hs v hv => ?_⟩
  obtain ⟨a,p,pair,ha,hp⟩ := supp s hs v hv
  exact ⟨a,p,pair,ha,sub p hp⟩

/-- 规范阶段名字的实际整列函数图及完整值域，供并名字和逐阶段求值共用。 -/
theorem rp_parts_l {ω A P R U : M.Domain} (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo I A ω U) (product : Fp_product_d hZF ω A P R) :
    ∃ D F, M.IsSetFunctionFromTo I F ω D ∧
      (∀ n s, Entry_d M n s F ↔ M.mem n ω ∧ Rp_part_d hZF ω A n s) ∧
      ∀ s, M.mem s D ↔ ∃ n, M.mem n ω ∧ Rp_part_d hZF ω A n s := by
  let ρ : Env M 2 := ⟨fun i => [ω,A].get i,fun _ => ω⟩
  let φ : BinarySchema 2 := { body := rp_part_m (.bound 2) (.bound 3) (.bound 1) .newest }
  have sat n s : φ.denote ρ n s ↔ Rp_part_d hZF ω A n s := rp_part_sat_l hZF ..
  have total n (hn : M.mem n ω) : ∃ s, φ.denote ρ n s := by
    obtain ⟨C,S,b,stage⟩ := product.stage_l hZF hw hn fa
    obtain ⟨s,name⟩ := rn_exists_l hZF stage.member
    exact ⟨s,(sat n s).mpr ⟨C,S,b,stage,name⟩⟩
  obtain ⟨D,range⟩ := ZF.exists_functionalImage hZF φ ρ ω total
    (fun n r s hr hs => ((sat n r).mp hr).unique_l hZF ((sat n s).mp hs))
  obtain ⟨F,fn,entries⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total
    (fun n _ r s hr hs => ((sat n r).mp hr).unique_l hZF ((sat n s).mp hs))
    (fun n s hn hs => (range s).mpr ⟨n,hn,hs⟩)
  exact ⟨D,F,fn,fun n s => (entries n s).trans (and_congr_right fun _ => sat n s),
    fun s => (range s).trans (exists_congr fun n => and_congr_right fun _ => sat n s)⟩

theorem rp_name_exists_l {ω A P R U : M.Domain} (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo I A ω U) (product : Fp_product_d hZF ω A P R) :
    ∃ r, Rp_name_d hZF ω A P r := by
  obtain ⟨D,_,_,_,range⟩ := rp_parts_l hZF hw fa product
  obtain ⟨r,union⟩ := KP.exists_union (ZF.modelsKP hZF) D
  have members v : M.mem v r ↔ ∃ n s, M.mem n ω ∧ Rp_part_d hZF ω A n s ∧ M.mem v s := by
    constructor
    · intro hv
      obtain ⟨s,hs,vs⟩ := (union v).mp hv
      obtain ⟨n,hn,ns⟩ := (range s).mp hs
      exact ⟨n,s,hn,ns,vs⟩
    · rintro ⟨n,s,hn,ns,vs⟩
      exact (union v).mpr ⟨s,(range s).mpr ⟨n,hn,ns⟩,vs⟩
  refine ⟨r,?_,members⟩
  apply (name_unfold_l M (name_ops_l M hZF) P r).mpr
  intro v hv
  obtain ⟨n,s,hn,⟨C,S,b,stage,⟨D,t,W,data⟩⟩,vs⟩ := (members v).mp hv
  have sub : M.MemberSubset C P := fun q hq => ((stage.stage.product_read_l hZF product hn).1 q).mp hq |>.1
  obtain ⟨a,p,pair,hp,na⟩ := (name_unfold_l M (name_ops_l M hZF) C s).mp data.name v vs
  exact ⟨a,p,pair,sub p hp,name_conditions_mono_l sub na⟩

theorem Rp_name_d.aut_fixed_l {ω A P R r F : M.Domain} (h : Rp_name_d hZF ω A P r)
    (product : Fp_product_d hZF ω A P R) (aut : Fp_aut_d I P R F) : Nmap_d M F r r := by
  obtain ⟨r',image⟩ := nmap_exists_l M hZF F r
  have fixed {n s} (hn : M.mem n ω) (part : Rp_part_d hZF ω A n s) : Nmap_d M F s s := by
    obtain ⟨C,S,b,stage,name⟩ := part
    exact aut.real_name_fixed_l hZF product stage hn name
  have eq : r' = r := hZF.1.eq_of_same_members r' r (fun v => by
    rw [nmap_mem_l M hZF.1 (check_ind_l M hZF) image]
    constructor
    · rintro ⟨a,p,c,q,⟨u,pair,hu⟩,ac,pq,vpair⟩
      obtain ⟨n,s,hn,part,us⟩ := (h.members u).mp hu
      have vs := (nmap_mem_l M hZF.1 (check_ind_l M hZF) (fixed hn part) v).mpr
        ⟨a,p,c,q,⟨u,pair,us⟩,ac,pq,vpair⟩
      exact (h.members v).mpr ⟨n,s,hn,part,vs⟩
    · intro hv
      obtain ⟨n,s,hn,part,vs⟩ := (h.members v).mp hv
      obtain ⟨a,p,c,q,⟨u,pair,us⟩,ac,pq,vpair⟩ := (nmap_mem_l M hZF.1 (check_ind_l M hZF) (fixed hn part) v).mp vs
      exact ⟨a,p,c,q,⟨u,pair,(h.members u).mpr ⟨n,s,hn,part,us⟩⟩,ac,pq,vpair⟩)
  exact eq ▸ image

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原有限前缀到全乘积的规范正则包含

包含图在条件上就是恒等。约减为原条件的有限限制；替换前缀产生共同加强。
泛型回拉是同一全乘积滤子的限制，名字因而保留原对象。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Fp_prefix_d.regular_l {ω A n C S P R : M.Domain}
    (stage : Fp_prefix_d hZF ω A n C S) (product : Fp_product_d hZF ω A P R) (hn : M.mem n ω) :
    ∃ Γ, Reg_map_d M C S C P R P Γ ∧ ∀ p q, Entry_d M p q Γ ↔ M.mem p C ∧ q = p := by
  obtain ⟨Γ,_,entries⟩ := aut_id_l hZF C S C
  have section₀ := stage.product_read_l hZF product hn
  have sub {p} (hp : M.mem p C) : M.mem p P := ((section₀.1 p).mp hp).1
  have nz {p B : M.Domain} (hp : M.mem p B) : p ≠ B := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hp)
  have lower {x p a : M.Domain} (fp : Fp_at_d I ω A n p)
      (cut : M.IsRestrictionOf I a x n) (le : Fp_le_d I x p) : Fp_le_d I a p := by
    intro i s is
    obtain ⟨t,it,st⟩ := le i s is
    exact ⟨t,(cut.2 i t).mpr ⟨(fp.domain i).mpr ⟨s,is⟩,it⟩,st⟩
  refine ⟨Γ,⟨fun p hp _ => ⟨p,(entries p p).mpr ⟨hp,rfl⟩⟩,?_,?_,?_,?_⟩,entries⟩
  · intro p q pq
    obtain ⟨hp,eq⟩ := (entries p q).mp pq
    subst q
    exact ⟨hp,nz hp,sub hp,nz (sub hp)⟩
  · intro p q x y px qy pq
    obtain ⟨hp,ex⟩ := (entries p x).mp px
    obtain ⟨hq,ey⟩ := (entries q y).mp qy
    subst x y
    exact (product.order p q).mpr ⟨sub hp,sub hq,((stage.order p q).mp pq).2.2⟩
  · intro p q x y px qy cmp
    obtain ⟨hp,ex⟩ := (entries p x).mp px
    obtain ⟨hq,ey⟩ := (entries q y).mp qy
    subst x y
    obtain ⟨z,zp,zq⟩ := cmp
    obtain ⟨m,_,fz⟩ := (product.conditions z).mp zp.1
    have fp := (stage.conditions p).mp hp
    have lp := ((product.order z p).mp zp.2.2).2.2
    obtain ⟨r,cut,fr⟩ := fz.restrict_l hZF (lp.domain_l I fz fp)
    have hr := (stage.conditions r).mpr fr
    exact ⟨r,⟨hr,nz hr,(stage.order r p).mpr ⟨hr,hp,lower fp cut lp⟩⟩,
      (stage.order r q).mpr ⟨hr,hq,lower ((stage.conditions q).mp hq) cut ((product.order z q).mp zq).2.2⟩⟩
  · intro x hx _ p y py xy
    obtain ⟨hp,ey⟩ := (entries p y).mp py
    subst y
    obtain ⟨m,hm,fx⟩ := (product.conditions x).mp hx
    have fp := (stage.conditions p).mp hp
    have le := ((product.order x p).mp xy).2.2
    have nm := le.domain_l I fx fp
    obtain ⟨r,cut,fr⟩ := fx.restrict_l hZF nm
    have hr := (stage.conditions r).mpr fr
    refine ⟨r,hr,nz hr,fun q z qz qr => ?_⟩
    obtain ⟨hq,ez⟩ := (entries q z).mp qz
    subst z
    obtain ⟨s,fs,_,sq,graph⟩ := fx.splice_l hZF ((stage.conditions q).mp hq) nm
    have sx := fp_splice_lower_l hZF cut ((stage.order q r).mp qr).2.2 graph
    have hs := (product.conditions s).mpr ⟨m,hm,fs⟩
    exact ⟨s,⟨hs,nz hs,(product.order s x).mpr ⟨hs,hx,sx⟩⟩,(product.order s q).mpr ⟨hs,sub hq,sq⟩⟩

theorem Fp_prefix_d.extension_l {ω A n C S P R U : M.Domain}
    (stage : Fp_prefix_d hZF ω A n C S) (product : Fp_product_d hZF ω A P R)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (fa : M.IsSetFunctionFromTo I A ω U)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G) :
    let H : M.Domain → Prop := fun p => M.mem p C ∧ G p
    let E := extension_l M hZF C S C H
    let D := extension_l M hZF P R P G
    Generic_d M C S C H ∧ ∃ e : E.Domain → D.Domain,
      Function.Injective e ∧ (∀ a y, D.mem y (e a) ↔ ∃ b, E.mem b a ∧ e b = y) ∧
      (∀ a t, Qval_d M C S C H t a → Qval_d M P R P G t (e a)) ∧
      ∀ x a, Gval_d M C S C H x a → Gval_d M P R P G x (e a) := by
  let H : M.Domain → Prop := fun p => M.mem p C ∧ G p
  have sub {p} (hp : M.mem p C) := ((stage.product_read_l hZF product hn).1 p).mp hp |>.1
  have projected : Fp_project_d I C G = H := by
    funext p
    apply propext
    exact ⟨fun ⟨hp,q,hq,qp⟩ => ⟨hp,generic.upward q p hq (sub hp)
      ((product.order q p).mpr ⟨(generic.proper q hq).1,sub hp,qp⟩)⟩,
      fun ⟨hp,hg⟩ => ⟨hp,p,hg,Fp_le_d.refl_l I p⟩⟩
  have small : Generic_d M C S C H := projected ▸ product.project_generic_l hZF hw hn fa stage generic
  obtain ⟨Γ,reg,entries⟩ := stage.regular_l hZF product hn
  have pull : Pull_generic_d M Γ G = H := funext fun p => propext
    ⟨fun ⟨q,pq,hq⟩ => ⟨((entries p q).mp pq).1,((entries p q).mp pq).2 ▸ hq⟩,
      fun ⟨hp,hg⟩ => ⟨p,(entries p p).mpr ⟨hp,rfl⟩,hg⟩⟩
  have inh : ∃ p, Pull_generic_d M Γ G p := pull.symm ▸ small.inhabited
  have lifted := stage_extension_l (stage.order_l hZF) (product.order_l hZF) hZF reg generic inh
  rw [pull] at lifted
  obtain ⟨e,values,full,inj⟩ := lifted
  have keep a t (ta : Qval_d M C S C H t a) := values a t t ta (nmap_identity_l hZF entries (qval_name_l ta))
  refine ⟨small,e,inj,full,keep,?_⟩
  rintro x a ⟨b,t,hb,check,ta⟩
  exact ⟨b,t,hb.2,check,keep a t ta⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 有限前缀名字补长而解释值不变

将能补到指定长度的标签替换为该长度的全部向下加强；无此加强的标签保留。
该关系在每个原条件以下预稠密，故名字的全乘积解释不变；原闭支撑
只含短标签，所以变换后的名字确实只使用指定较长前缀的条件。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

private theorem fp_longer_l {ω A P R m D T W r : M.Domain}
    (hw : M.IsOmega ω) (hm : M.mem m ω) (fa : M.IsSetFunctionFromTo I A ω W)
    (product : Fp_product_d hZF ω A P R) (stage : Fp_prefix_d hZF ω A m D T) (hr : M.mem r P) :
    ∃ s q, M.mem s P ∧ Fp_le_d I s r ∧ M.mem q D ∧ M.IsRestrictionOf I q s m := by
  obtain ⟨k,hk,fr⟩ := (product.conditions r).mp hr
  have restrict (sub : M.MemberSubset m k) := fr.restrict_l hZF sub
  rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare m hm k hk with eq | mk | km
  · obtain ⟨q,cut,fq⟩ := restrict (fun i hi => (eq i).mp hi)
    exact ⟨r,q,hr,Fp_le_d.refl_l I r,(stage.conditions q).mpr fq,cut⟩
  · obtain ⟨q,cut,fq⟩ := restrict ((hw.members_areOrdinals (ZF.modelsKP hZF) k hk).transitive m mk)
    exact ⟨r,q,hr,Fp_le_d.refl_l I r,(stage.conditions q).mpr fq,cut⟩
  · obtain ⟨s,fs,_,sr⟩ := fr.pad_l hZF hw hm fa ((hw.members_areOrdinals (ZF.modelsKP hZF) m hm).transitive k km)
    exact ⟨s,s,(product.conditions s).mpr ⟨m,hm,fs⟩,sr,(stage.conditions s).mpr fs,
      fs.function.1,fun i a => ⟨fun ia => ⟨(fs.domain i).mpr ⟨a,ia⟩,ia⟩,And.right⟩⟩

theorem Fp_prefix_d.name_extend_l {ω A P R W n m C S D T τ : M.Domain} {G : M.Domain → Prop}
    (hw : M.IsOmega ω) (hn : M.mem n ω) (hm : M.mem m ω) (fa : M.IsSetFunctionFromTo I A ω W)
    (product : Fp_product_d hZF ω A P R) (stage : Fp_prefix_d hZF ω A n C S)
    (later : Fp_prefix_d hZF ω A m D T) (sub : M.MemberSubset n m)
    (generic : Generic_d M P R P G) (name : Name_d M C τ)
    {y : (Model.Forcing.Internal.extension_l M hZF P R P G).Domain} (value : Qval_d M P R P G τ y) :
    ∃ σ, Name_d M D σ ∧ Qval_d M P R P G σ y := by
  have O := product.order_l hZF
  have nz {p} (hp : M.mem p P) : p ≠ P := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) P (eq ▸ hp)
  have cP : M.MemberSubset C P := fun p hp => ((stage.product_read_l hZF product hn).1 p).mp hp |>.1
  have dP : M.MemberSubset D P := fun p hp => ((later.product_read_l hZF product hm).1 p).mp hp |>.1
  let ρ : Env M 2 := ⟨Fin.cases D (fun _ => R),fun _ => D⟩
  let φ : BinarySchema 2 := { body := (.disj
    (.conj (.mem .newest (.bound 2)) (entry_m .newest (.bound 1) (.bound 3)))
    (.conj (.neg (Formula.existsMem (.bound 2) (entry_m .newest (.bound 2) (.bound 4))))
      (Formula.extensionalEq .newest (.bound 1)))) }
  have sat p q : φ.denote ρ p q ↔ (M.mem q D ∧ Entry_d M q p R) ∨
      (¬ (∃ s, M.mem s D ∧ Entry_d M s p R)) ∧ q = p := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_disj_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff,entry_sat_l M hZF.1,Formula.satisfies_neg_iff,
      Formula.satisfies_existsMem_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  obtain ⟨Γ,_,edges⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ P
  have read p q := (edges p q).trans (and_congr_right fun _ => and_congr_right fun _ => sat p q)
  have bound p q (pq : Entry_d M p q Γ) : M.mem p P ∧ Below_d M P R P q p := by
    obtain ⟨hp,hq,case⟩ := (read p q).mp pq
    exact ⟨hp,hq,nz hq,case.elim And.right (fun h => h.2.symm ▸ O.refl p hp)⟩
  have dense p (hp : M.mem p P) (_ : p ≠ P) r (rp : Below_d M P R P r p) :
      ∃ q s, Entry_d M p q Γ ∧ Below_d M P R P s r ∧ Entry_d M s q R := by
    classical
    by_cases short : ∃ q, M.mem q D ∧ Entry_d M q p R
    · obtain ⟨q₀,hq₀,q₀p⟩ := short
      obtain ⟨k,_,fp⟩ := (product.conditions p).mp hp
      have km := ((product.order q₀ p).mp q₀p).2.2.domain_l I ((later.conditions q₀).mp hq₀) fp
      obtain ⟨s,q,hs,sr,hq,cut⟩ := fp_longer_l hZF hw hm fa product later rp.1
      have sp := sr.trans_l I ((product.order r p).mp rp.2.2).2.2
      have qp : Fp_le_d I q p := by
        intro i a ia
        obtain ⟨b,ib,ab⟩ := sp i a ia
        exact ⟨b,(cut.2 i b).mpr ⟨km i ((fp.domain i).mpr ⟨a,ia⟩),ib⟩,ab⟩
      have qpR := (product.order q p).mpr ⟨dP q hq,hp,qp⟩
      have sq : Fp_le_d I s q := fun i a ia => ⟨a,((cut.2 i a).mp ia).2,fun _ h => h⟩
      exact ⟨q,s,(read p q).mpr ⟨hp,dP q hq,Or.inl ⟨hq,qpR⟩⟩,
        ⟨hs,nz hs,(product.order s r).mpr ⟨hs,rp.1,sr⟩⟩,(product.order s q).mpr ⟨hs,dP q hq,sq⟩⟩
    · exact ⟨p,r,(read p p).mpr ⟨hp,hp,Or.inr ⟨short,rfl⟩⟩,below_refl_l O rp.1 rp.2.1,rp.2.2⟩
  have labels p q (hp : M.mem p C) (pq : Entry_d M p q Γ) : M.mem q D := by
    obtain ⟨q₀,fq₀,_,q₀p⟩ := ((stage.conditions p).mp hp).pad_l hZF hw hm fa sub
    have hq₀ := (later.conditions q₀).mpr fq₀
    have edge := (product.order q₀ p).mpr ⟨dP q₀ hq₀,cP p hp,q₀p⟩
    exact ((read p q).mp pq).2.2.elim And.left (fun h => (h.1 ⟨q₀,hq₀,edge⟩).elim)
  obtain ⟨σ,map⟩ := nmap_exists_l M hZF Γ τ
  have targetName := nmap_support_name_l hZF labels name map
  obtain ⟨z,targetValue⟩ := name_value_l (R := R) (z := P) (U := G) (name_conditions_mono_l dP targetName)
  obtain ⟨p,gp⟩ := generic.inhabited
  have forced := nmap_refine_force_l O hZF bound dense (name_conditions_mono_l cP name) map (generic.proper p gp).1
  have eq : y = z := (qval_eq_l O hZF generic value targetValue).mp ⟨p,gp,forced⟩
  exact ⟨σ,targetName,eq.symm ▸ targetValue⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原有限前缀实数并名字属于同一低秩层

在实际秩模型内一次收集全部检查基点的名字库。检查名字绝对性和秩层的
子集闭包把每个背景候选名字回收，故原实数并名字包含于一个低秩乘积。
不要求力迫关系在秩模型与背景之间绝对，也不假定名字已经具有秩界。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rp_name_d.rank_mem_l {c X S δ ω A P R σ : M.Domain}
    (source : Smem_d I c X S) (rank : V_d I δ X) (limit : M.IsLimitOrdinal δ)
    (native : (smdl_structure_l I (R := S) source.1.2.1).Models ZF)
    (hω : M.mem ω X) (hP : M.mem P X)
    (product : Fp_product_d hZF ω A P R) (name : Rp_name_d hZF ω A P σ) : M.mem σ X := by
  let N := smdl_structure_l I (R := S) source.1.2.1
  let J := kp_pair_l (ZF.modelsKP native)
  have trans := v_transitive_l I rank
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have member {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b :=
    image_member_l (M := N) (N := M) Subtype.val inj full
  let ω₀ : N.Domain := ⟨ω,hω⟩
  let P₀ : N.Domain := ⟨P,hP⟩
  obtain ⟨D₀,square⟩ := ZF.exists_cartesianProduct native J ω₀ ω₀
  have square' := image_product_l (hEN := hZF.1) (hPN := KP.exists_pair (ZF.modelsKP hZF)) Subtype.val inj full square
  obtain ⟨U,pools⟩ := ck_pools_l native P₀ D₀
  obtain ⟨B,rectangle⟩ := ZF.exists_cartesianProduct hZF I U.val P
  apply v_subset_mem_l I rank (ZF.v_product_mem_l I hZF rank limit U.property hP rectangle)
  intro v hv
  obtain ⟨n,t,hn,⟨C,T,b,stage,real⟩,vt⟩ := (name.members v).mp hv
  obtain ⟨D,w,Q,data⟩ := real
  have sameD : D = D₀.val := hZF.1.eq_of_same_members _ _ (fun x => (data.product x).trans (square' x).symm)
  have sub : M.MemberSubset C P := fun q hq =>
    (product.conditions q).mpr ⟨n,hn,(stage.stage.conditions q).mp hq⟩
  obtain ⟨a,p,pair,_,_⟩ := (name_unfold_l M (name_ops_l M hZF) C t).mp data.name v vt
  obtain ⟨ha,hp,_⟩ := (data.entries a p).mp ⟨v,pair,vt⟩
  have hb := sub b stage.member
  let b₀ : N.Domain := ⟨b,trans P hP b hb⟩
  have hb₀ : N.mem b₀ P₀ := member.mp hb
  have bound : Ck_bound_d P b D₀.val a := by
    intro q hq
    obtain ⟨s,p,d,pair,hp,hd,check⟩ := (data.pool a).mp ha q hq
    exact ⟨s,p,d,pair,sub p hp,sameD ▸ hd,check⟩
  obtain ⟨V,pool⟩ := ck_pool_exists_l native hb₀ D₀
  have pool' := Smem_d.check_pool_l hZF source trans rank native pool
  have haV : M.mem a V.val := (pool' a).mpr bound
  let a₀ : N.Domain := ⟨a,trans V.val V.property a haV⟩
  have nativeBound : Ck_bound_d P₀ b₀ D₀ a₀ :=
    (image_ck_bound_l native hZF Subtype.val inj full).mpr bound
  have haU : M.mem a U.val := member.mpr ((pools a₀).mpr ⟨b₀,hb₀,nativeBound⟩)
  exact (rectangle v).mpr ⟨a,haU,p,sub p hp,pair⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 规范实数并名字恰解释为全部有限前缀扩张的实数

同一个前缀名字在两侧解释，由规范正则包含给出的成员满嵌入逐名字对应。
因此下述并集既不漏掉前缀实数，也不额外加入整个全乘积扩张的新实数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

def Rp_value_d (ω A P R : M.Domain) (G : M.Domain → Prop)
    (x : (extension_l M hZF P R P G).Domain) : Prop :=
  ∃ n C S b, M.mem n ω ∧ Fp_stage_d hZF ω A n C S b ∧
    let H : M.Domain → Prop := fun p => M.mem p C ∧ G p
    let E := extension_l M hZF C S C H
    ∃ j : M.Domain → E.Domain, (∀ a, Gval_d M C S C H a (j a)) ∧
      ∃ τ y, Qval_d M C S C H τ y ∧ Qval_d M P R P G τ x ∧ Fn0_d (j ω) (j ω) y

theorem Rp_name_d.value_l {ω A P R U r : M.Domain} (h : Rp_name_d hZF ω A P r)
    (hw : M.IsOmega ω) (fa : M.IsSetFunctionFromTo I A ω U) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G) :
    ∃ Z : (extension_l M hZF P R P G).Domain, Qval_d M P R P G r Z ∧
      ∀ x, x ∈ Z ↔ Rp_value_d hZF ω A P R G x := by
  let D := extension_l M hZF P R P G
  have O := product.order_l hZF
  obtain ⟨Z,value⟩ := name_value_l (R := R) (z := P) (U := G) h.name
  refine ⟨Z,value,fun x => ⟨?_,?_⟩⟩
  · intro hx
    obtain ⟨τ,p,⟨v,pair,vr⟩,hp,τx⟩ := (qval_mem_l O hZF generic value).mp hx
    obtain ⟨n,s,hn,⟨C,S,b,stage,⟨D₀,t,W,data⟩⟩,vs⟩ := (h.members v).mp vr
    let H : M.Domain → Prop := fun p => M.mem p C ∧ G p
    let E := extension_l M hZF C S C H
    obtain ⟨small,e,_,full,keep,_⟩ := stage.stage.extension_l hZF product hw hn fa generic
    obtain ⟨q,hq⟩ := small.inhabited
    have hb := small.upward q b hq stage.member (stage.top q (small.proper q hq).1)
    obtain ⟨j,ground,Y,sy,reals⟩ := data.value_l hZF (stage.stage.order_l hZF) small hb
    have target := keep Y s sy
    have xY : D.mem x (e Y) := (qval_mem_l O hZF generic target).mpr ⟨τ,p,⟨v,pair,vs⟩,hp,τx⟩
    obtain ⟨y,hy,eq⟩ := (full Y x).mp xY
    obtain ⟨u,_,uy⟩ := value_name_l y
    exact ⟨n,C,S,b,hn,stage,j,ground,u,y,uy,eq ▸ keep y u uy,(reals y).mp hy⟩
  · rintro ⟨n,C,S,b,hn,stage,j,ground,τ,y,τy,τx,fy⟩
    obtain ⟨s,D₀,t,W,data⟩ := rn_exists_l hZF stage.member (R := S) (ω := ω)
    obtain ⟨small,e,_,full,keep,_⟩ := stage.stage.extension_l hZF product hw hn fa generic
    obtain ⟨q,hq⟩ := small.inhabited
    have hb := small.upward q b hq stage.member (stage.top q (small.proper q hq).1)
    obtain ⟨j₀,ground₀,Y,sy,reals⟩ := data.value_l hZF (stage.stage.order_l hZF) small hb
    have eqω := (ground ω).unique_l (stage.stage.order_l hZF) hZF small (ground₀ ω)
    have yY := (reals y).mpr (eqω ▸ fy)
    have xY : D.mem x (e Y) := qval_unique_l (keep y τ τy) τx ▸ (full Y (e y)).mpr ⟨y,yY,rfl⟩
    obtain ⟨u,p,⟨v,pair,vs⟩,hp,ux⟩ := (qval_mem_l O hZF generic (keep Y s sy)).mp xY
    exact (qval_mem_l O hZF generic value).mpr ⟨u,p,
      ⟨v,pair,(h.members v).mpr ⟨n,s,hn,⟨C,S,b,stage,D₀,t,W,data⟩,vs⟩⟩,hp,ux⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 每个原地实数都属于同一规范有限前缀实数并

在实际零前缀取同一个检查名字。前缀与全乘积的规范地映射解释它，
成员满性保持完整函数图，因而此名字已经给出 R* 中的原地实数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rp_name_d.ground_real_l {ω A P R W σ x : M.Domain}
    (name : Rp_name_d hZF ω A P σ) (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    (j : M.Domain → (extension_l M hZF P R P G).Domain)
    (ground : ∀ a, Gval_d M P R P G a (j a))
    {Z : (extension_l M hZF P R P G).Domain} (value : Qval_d M P R P G σ Z)
    (real : Fn0_d ω ω x) : (extension_l M hZF P R P G).mem (j x) Z := by
  obtain ⟨n,_,hn⟩ := hw.1.1
  obtain ⟨C,S,b,stage⟩ := product.stage_l hZF hw hn fa
  have small := (stage.stage.extension_l hZF product hw hn fa generic).1
  obtain ⟨p,hp⟩ := small.inhabited
  obtain ⟨k,checks,full,inj⟩ := check_map_l (stage.stage.order_l hZF) hZF small hp
  have base a := (gval_check_map_l (stage.stage.order_l hZF) hZF small hp k checks a (k a)).mpr rfl
  obtain ⟨τ,check,_,_⟩ := zf_check_l M hZF hp.1 x
  obtain ⟨l,checks',_,_⟩ := check_map_l (product.order_l hZF) hZF generic hp.2
  have eq : l x = j x := (gval_check_map_l (product.order_l hZF) hZF generic hp.2 l checks' x (l x)).mpr rfl
    |>.unique_l (product.order_l hZF) hZF generic (ground x)
  have fn := fn0_of_function_l (ZF.modelsKP (preserves_zf_l (stage.stage.order_l hZF) hZF small))
    (image_function_l k inj full (fn0_function_l (ZF.modelsKP hZF) real))
  have old : Rp_value_d hZF ω A P R G (j x) :=
    ⟨n,C,S,b,hn,stage,k,base,τ,k x,checks x τ check,eq ▸ checks' x τ check,fn⟩
  obtain ⟨Z',value',members⟩ := name.value_l hZF hw fa product generic
  exact qval_unique_l value' value ▸ (members (j x)).mpr old

end YesMetaZFC.Model.Forcing.Internal

/-! ## 任意前缀呈示中的实数进入同一规范实数并

旧顺序与规范顺序可以有不同集合编码；恒等条件图给出实际正则比较，
保留原名字和原泛型。随后以成员满嵌入运输完整函数图。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Fp_prefix_d.real_value_l {ω A P R U n C S τ : M.Domain}
    (stage : Fp_prefix_d hZF ω A n C S) (hw : M.IsOmega ω) (hn : M.mem n ω)
    (fa : M.IsSetFunctionFromTo I A ω U) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    (j : M.Domain → (Model.Forcing.Internal.extension_l M hZF C S C (fun p => M.mem p C ∧ G p)).Domain)
    (ground : ∀ a, Gval_d M C S C (fun p => M.mem p C ∧ G p) a (j a))
    {y : (Model.Forcing.Internal.extension_l M hZF C S C (fun p => M.mem p C ∧ G p)).Domain}
    {x : (Model.Forcing.Internal.extension_l M hZF P R P G).Domain}
    (value : Qval_d M C S C (fun p => M.mem p C ∧ G p) τ y)
    (target : Qval_d M P R P G τ x) (fn : Fn0_d (j ω) (j ω) y) :
    Rp_value_d hZF ω A P R G x := by
  obtain ⟨D,T,b,canonical⟩ := product.stage_l hZF hw hn fa
  have eq : D = C := hZF.1.eq_of_same_members D C
    (fun p => (canonical.stage.conditions p).trans (stage.conditions p).symm)
  subst D
  let H : M.Domain → Prop := fun p => M.mem p C ∧ G p
  have O := stage.order_l hZF
  have L := canonical.stage.order_l hZF
  have order p q : Entry_d M p q S ↔ Entry_d M p q T :=
    (stage.order p q).trans (canonical.stage.order p q).symm
  obtain ⟨Γ,_,entries⟩ := aut_id_l hZF C S C
  have nz {p} (hp : M.mem p C) : p ≠ C := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ hp)
  have reg : Reg_map_d M C S C C T C Γ := by
    refine ⟨fun p hp _ => ⟨p,(entries p p).mpr ⟨hp,rfl⟩⟩,?_,?_,?_,?_⟩
    · intro p q pq
      obtain ⟨hp,rfl⟩ := (entries p q).mp pq
      exact ⟨hp,nz hp,hp,nz hp⟩
    · intro p q x y px qy pq
      obtain ⟨_,ex⟩ := (entries p x).mp px
      obtain ⟨_,ey⟩ := (entries q y).mp qy
      subst x y
      exact (order p q).mp pq
    · intro p q x y px qy cmp
      obtain ⟨_,ex⟩ := (entries p x).mp px
      obtain ⟨_,ey⟩ := (entries q y).mp qy
      subst x y
      obtain ⟨z,zp,zq⟩ := cmp
      exact ⟨z,⟨zp.1,zp.2.1,(order z p).mpr zp.2.2⟩,(order z q).mpr zq⟩
    · intro x hx _ p y _ _
      refine ⟨x,hx,nz hx,fun q z qz qx => ?_⟩
      obtain ⟨hq,ez⟩ := (entries q z).mp qz
      subst z
      exact ⟨q,⟨hq,nz hq,(order q x).mp qx⟩,L.refl q hq⟩
  have small := (canonical.stage.extension_l hZF product hw hn fa generic).1
  have pull : Pull_generic_d M Γ H = H := funext fun p => propext
    ⟨fun ⟨q,pq,hq⟩ => ((entries p q).mp pq).2 ▸ hq,
      fun hp => ⟨p,(entries p p).mpr ⟨hp.1,rfl⟩,hp⟩⟩
  have lifted := stage_extension_l O L hZF reg small (pull.symm ▸ small.inhabited)
  rw [pull] at lifted
  obtain ⟨e,values,full,inj⟩ := lifted
  have keep a t (ta : Qval_d M C S C H t a) :=
    values a t t ta (nmap_identity_l hZF entries (qval_name_l ta))
  have ground' a : Gval_d M C T C H a (e (j a)) := by
    obtain ⟨p,t,hp,check,val⟩ := ground a
    exact ⟨p,t,hp,check,keep (j a) t val⟩
  have old := preserves_zf_l O hZF (stage.extension_l hZF product hw hn fa generic).1
  have new := preserves_zf_l L hZF small
  exact ⟨n,C,T,b,hn,canonical,e ∘ j,ground',τ,e y,keep y τ value,target,
    fn0_of_function_l (ZF.modelsKP new) (image_function_l e inj full (fn0_function_l (ZF.modelsKP old) fn))⟩

theorem Rp_value_d.function_l {ω A P R U : M.Domain}
    (hw : M.IsOmega ω) (fa : M.IsSetFunctionFromTo I A ω U) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    (j : M.Domain → (extension_l M hZF P R P G).Domain)
    (ground : ∀ a, Gval_d M P R P G a (j a))
    {x : (extension_l M hZF P R P G).Domain} (real : Rp_value_d hZF ω A P R G x) :
    Fn0_d (j ω) (j ω) x := by
  obtain ⟨n,C,S,b,hn,stage,k,ground₀,τ,y,value,target,fn⟩ := real
  obtain ⟨small,e,inj,full,keep,base⟩ := stage.stage.extension_l hZF product hw hn fa generic
  have old := preserves_zf_l (stage.stage.order_l hZF) hZF small
  have new := preserves_zf_l (product.order_l hZF) hZF generic
  have commute a : e (k a) = j a := (base a (k a) (ground₀ a)).unique_l (product.order_l hZF) hZF generic (ground a)
  have eq : e y = x := qval_unique_l (keep y τ value) target
  have image := fn0_of_function_l (ZF.modelsKP new) (image_function_l e inj full (fn0_function_l (ZF.modelsKP old) fn))
  simpa only [commute,eq] using image

end YesMetaZFC.Model.Forcing.Internal

/-! ## 查询实数与二值码的同一有限前缀名字

在原查询点所在的有限前缀扩张内构造二值码及其真实名字。
正则包含把原名字和编码名字同时送入全乘积扩张，规范解码在此包含下保持。
编码属于原规范实数并，不将全乘积中的任意新实数加入派生基集。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 每个有限阶段实数的实际二值编码仍位于同一阶段，且两张名字在全扩张中
分别解释为原点及其编码。这里只消费原泛型，不另换扩张。 -/
theorem Rp_value_d.binary_l {ω A P R W : M.Domain}
    (hw : M.IsOmega ω) (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    (j : M.Domain → (extension_l M hZF P R P G).Domain)
    (ground : ∀ a, Gval_d M P R P G a (j a))
    {x : (extension_l M hZF P R P G).Domain} (real : Rp_value_d hZF ω A P R G x) :
    let E := extension_l M hZF P R P G
    let hE := preserves_zf_l (product.order_l hZF) hZF generic
    ∃ b : E.Domain, Rp_value_d hZF ω A P R G b ∧ Bc_binary_d (j ω) b ∧
      Bc_read_d (kp_pair_l (ZF.modelsKP hE)) (j ω) b x ∧
      ∃ n C S τ σ, M.mem n ω ∧ Fp_prefix_d hZF ω A n C S ∧ Name_d M C τ ∧ Name_d M C σ ∧
        Qval_d M P R P G τ x ∧ Qval_d M P R P G σ b := by
  dsimp only
  obtain ⟨n,C,S,o,hn,stage,k,ground₀,τ,y,value,target,fn⟩ := real
  let H : M.Domain → Prop := fun p => M.mem p C ∧ G p
  let D := extension_l M hZF C S C H
  let E := extension_l M hZF P R P G
  obtain ⟨small,e,ei,ef,keep,base⟩ := stage.stage.extension_l hZF product hw hn fa generic
  have hD : D.Models ZF := preserves_zf_l (stage.stage.order_l hZF) hZF small
  have hE : E.Models ZF := preserves_zf_l (product.order_l hZF) hZF generic
  have commute a : e (k a) = j a :=
    (base a (k a) (ground₀ a)).unique_l (product.order_l hZF) hZF generic (ground a)
  have same : e y = x := qval_unique_l (keep y τ value) target
  obtain ⟨p,hp⟩ := small.inhabited
  obtain ⟨k₀,checks,full,inj⟩ := check_map_l (stage.stage.order_l hZF) hZF small hp
  have eqw : k₀ ω = k ω := (gval_check_map_l (stage.stage.order_l hZF) hZF small hp k₀ checks ω (k ω)).mp (ground₀ ω)
  have omega : D.IsOmega (k ω) := eqw ▸ image_omega_l (hEN := hD.1) k₀ inj full hZF
    (internal_foundation_l (stage.stage.order_l hZF) hZF small) hw
    (fun T => KP.difference_exists_d (ZF.modelsKP hD) T (k₀ ω))
  obtain ⟨b,binary,read⟩ := bc_encode_l hD omega fn
  obtain ⟨σ,ns,val⟩ := value_name_l b
  have targetBinary : Bc_binary_d (j ω) (e b) := by
    simpa only [commute] using (bc_binary_image_l e ei ef hD.1 hE.1).mp binary
  have targetRead : Bc_read_d (kp_pair_l (ZF.modelsKP hE)) (j ω) (e b) x := by
    simpa only [commute,same] using (bc_read_image_l e ei ef hD hE (omega.isOrdinal (ZF.modelsKP hD))).mp read
  exact ⟨e b,⟨n,C,S,o,hn,stage,k,ground₀,σ,b,val,keep b σ val,binary.1⟩,
    targetBinary,targetRead,n,C,S,τ,σ,hn,stage.stage,qval_name_l value,ns,target,keep b σ val⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 规范前缀实数并与背景函数图的双向唯一对应

有限前缀的原名字经同一正则包含进入全扩张，完整函数图沿该包含保持。
反向从规范名字成员的实际前缀解释分离背景图，故两个方向共用原泛型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hM : M.Models ZF) {c X R : M.Domain}
  (source : Smem_d (kp_pair_l (ZF.modelsKP hM)) c X R) (trans : M.TransitiveSet X)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1).Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "N" => smdl_structure_l I (R := R) (And.left (And.right (And.left source)))

/-- 背景实数由某一实际有限前缀中的原函数名字解释。 -/
def Rp_bg_d (ω A T : (N).Domain) (H x : M.Domain) : Prop :=
  Fn0_d ω.val ω.val x ∧ ∃ n C S E : (N).Domain, ∃ K : M.Domain,
    (N).mem n ω ∧ Fp_prefix_d native ω A n C S ∧
      Fp_filter_project_d C.val T.val H K ∧ Fn_bg_d X C.val S.val C.val ω.val E.val K x

include trans in
theorem rp_background_l {ω A P T U : (N).Domain} {H : M.Domain}
    (hw : (N).IsOmega ω) (fa : (N).IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) A ω U)
    (product : Fp_product_d native ω A P T) (generic : Gset_d P.val T.val P.val X H) :
    let G : (N).Domain → Prop := fun p => M.mem p.val H
    let E := extension_l N native P T P G
    ∃ j : (N).Domain → E.Domain, (∀ a, Gval_d N P T P G a (j a)) ∧
      (∀ y, Rp_value_d native ω A P T G y → Fn0_d (j ω) (j ω) y ∧
        ∃ x, (Rp_bg_d hM source native ω A T H x ∧ Fn_read_d Subtype.val j y x) ∧
          ∀ z, (Rp_bg_d hM source native ω A T H z ∧ Fn_read_d Subtype.val j y z) → z = x) ∧
      ∀ x, Rp_bg_d hM source native ω A T H x →
        ∃ y, (Rp_value_d native ω A P T G y ∧ Fn_read_d Subtype.val j y x) ∧
          ∀ z, (Rp_value_d native ω A P T G z ∧ Fn_read_d Subtype.val j z x) → z = y := by
  let G : (N).Domain → Prop := fun p => M.mem p.val H
  let E := extension_l N native P T P G
  have O := product.order_l native
  obtain ⟨sub,g⟩ := (source.generic_code_l I hM.1 trans (ZF.modelsKP native) P T P H).mp generic
  have hE := preserves_zf_l O native g
  have ni : Function.Injective (Subtype.val : (N).Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have nf := smem_full_l I source trans
  obtain ⟨p,hp⟩ := g.inhabited
  obtain ⟨j,checks,jf,_⟩ := check_map_l O native g hp
  have ground a := (gval_check_map_l O native g hp j checks a (j a)).mpr rfl
  -- 背景投影集合与原泛型的前缀限制是同一个滤子。
  have project {n C S : (N).Domain} {K : M.Domain} (hn : (N).mem n ω)
      (stage : Fp_prefix_d native ω A n C S) (projection : Fp_filter_project_d C.val T.val H K) :
      (fun p : (N).Domain => M.mem p.val K) = (fun p => (N).mem p C ∧ G p) := by
    funext p
    apply propext
    rw [Smem_d.project_filter_read_l hM source trans native product stage hn sub projection p]
    constructor
    · rintro ⟨hc,q,hq,le⟩
      have hp := ((stage.product_read_l native product hn).1 p).mp hc |>.1
      exact ⟨hc,g.upward q p hq hp ((product.order q p).mpr ⟨(g.proper q hq).1,hp,le⟩)⟩
    · rintro ⟨hc,hg⟩
      exact ⟨hc,p,hg,Fp_le_d.refl_l (kp_pair_l (ZF.modelsKP native)) p⟩
  -- 名字值的每个成员先在原前缀读取，再沿同一包含送入全扩张。
  have forward (y : E.Domain) (real : Rp_value_d native ω A P T G y) :
      ∃ x, Rp_bg_d hM source native ω A T H x ∧ Fn_read_d Subtype.val j y x := by
    obtain ⟨n,C,S,b,hn,stage,k,base,τ,z,value,target,fn⟩ := real
    obtain ⟨K,projection,gK⟩ := Smem_d.product_project_l hM source trans native hw hn fa product stage.stage generic
    have eqG := project hn stage.stage projection
    have all := real_values_background_l hM source trans native (ω := ω) (stage.stage.order_l native) gK
    dsimp only at all
    rw [eqG] at all
    obtain ⟨k₀,base₀,values⟩ := all
    obtain ⟨small,e,ei,ef,keep,baseE⟩ := stage.stage.extension_l native product hw hn fa g
    have eqk : k₀ = k := funext fun a => (base₀ a).unique_l (stage.stage.order_l native) native small (base a)
    subst k₀
    obtain ⟨x,fx,code,read⟩ := values z fn
    have commute : e ∘ k = j := funext fun a => (baseE a (k a) (base a)).unique_l O native g (ground a)
    have eq : e z = y := qval_unique_l (keep z τ value) target
    have moved := read.image_l (KP.exists_pair (ZF.modelsKP (preserves_zf_l (stage.stage.order_l native) native small))) hE.1 e ei ef
    rw [commute,eq] at moved
    exact ⟨x,⟨fx,n,C,S,ω,K,hn,stage.stage,projection,code⟩,moved⟩
  -- 反向保留背景证书中的原名字；顺序规范化不更换滤子或函数图。
  have backward (x : M.Domain) (real : Rp_bg_d hM source native ω A T H x) :
      ∃ y, Rp_value_d native ω A P T G y ∧ Fn_read_d Subtype.val j y x := by
    obtain ⟨fx,n,C,S,D,K,hn,stage,projection,code⟩ := real
    have eqG := project hn stage projection
    have old := (fn_bg_read_l I hM.1 source trans native.1 C S C ω D K x).mp code
    rw [eqG] at old
    obtain ⟨small,e,ei,ef,keep,baseE⟩ := stage.extension_l native product hw hn fa g
    obtain ⟨τ,k,y,value,base,fn,read⟩ := old.real_value_l (ZF.modelsKP hM) native Subtype.val ni nf
      (stage.order_l native) small fx
    have commute : e ∘ k = j := funext fun a => (baseE a (k a) (base a)).unique_l O native g (ground a)
    have moved := read.image_l (KP.exists_pair (ZF.modelsKP (preserves_zf_l (stage.order_l native) native small))) hE.1 e ei ef
    rw [commute] at moved
    exact ⟨e y,stage.real_value_l native hw hn fa product g k base value (keep y τ value) fn,moved⟩
  refine ⟨j,ground,?_,?_⟩
  · intro y real
    obtain ⟨x,fx,read⟩ := forward y real
    refine ⟨real.function_l native hw fa product g j ground,x,⟨fx,read⟩,fun z hz => ?_⟩
    exact hz.2.unique_l (ZF.modelsKP hM) read (fn0_function_l (ZF.modelsKP hM) hz.1.1).1.1
      (fn0_function_l (ZF.modelsKP hM) fx.1).1.1
  · intro x real
    obtain ⟨y,fy,read⟩ := backward x real
    refine ⟨y,⟨fy,read⟩,fun z hz => ?_⟩
    exact hz.2.value_unique_l hE.1 ni jf
      (hz.1.function_l native hw fa product g j ground) (fy.function_l native hw fa product g j ground) read

end YesMetaZFC.Model.Forcing.Internal

/-! ## 背景查询点及其二值码的同前缀名字工厂

从原背景实数的前缀证书恢复同一全泛型中的查询点，在其原阶段编码，
再由背景图分离恢复编码实数。完整图比较证明它解码为原指定查询点。
结论同时保留两张同阶段名字、扩张中的解码和背景中的解码。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hM : M.Models ZF) {c X R : M.Domain}
  (source : Smem_d (kp_pair_l (ZF.modelsKP hM)) c X R) (trans : M.TransitiveSet X)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1).Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "N" => smdl_structure_l I (R := R) (And.left (And.right (And.left source)))

theorem Rp_bg_d.binary_l {ω A P T U : (N).Domain} {H x : M.Domain}
    (hw : (N).IsOmega ω) (fa : (N).IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) A ω U)
    (product : Fp_product_d native ω A P T) (generic : Gset_d P.val T.val P.val X H)
    (real : Rp_bg_d hM source native ω A T H x) :
    let G : (N).Domain → Prop := fun p => M.mem p.val H
    let E := extension_l N native P T P G
    let g := ((source.generic_code_l I hM.1 trans (ZF.modelsKP native) P T P H).mp generic).2
    let hE := preserves_zf_l (product.order_l native) native g
    ∃ b, Rp_bg_d hM source native ω A T H b ∧ Bc_binary_d ω.val b ∧ Bc_read_d I ω.val b x ∧
      ∃ j : (N).Domain → E.Domain, (∀ a, Gval_d N P T P G a (j a)) ∧ ∃ y z : E.Domain,
        Rp_value_d native ω A P T G y ∧ Rp_value_d native ω A P T G z ∧
        Fn_read_d Subtype.val j y x ∧ Fn_read_d Subtype.val j z b ∧ Bc_binary_d (j ω) z ∧
        Bc_read_d (kp_pair_l (ZF.modelsKP hE)) (j ω) z y ∧
        ∃ n C S τ σ : (N).Domain, (N).mem n ω ∧ Fp_prefix_d native ω A n C S ∧
          Name_d N C τ ∧ Name_d N C σ ∧ Qval_d N P T P G τ y ∧ Qval_d N P T P G σ z := by
  dsimp only
  let G : (N).Domain → Prop := fun p => M.mem p.val H
  let E := extension_l N native P T P G
  have g := ((source.generic_code_l I hM.1 trans (ZF.modelsKP native) P T P H).mp generic).2
  have O := product.order_l native
  have hE : E.Models ZF := preserves_zf_l O native g
  obtain ⟨j,ground,forward,backward⟩ := rp_background_l hM source trans native hw fa product generic
  obtain ⟨y,⟨ry,readY⟩,_⟩ := backward x real
  obtain ⟨z,rz,binary,decode,n,C,S,τ,σ,hn,stage,nt,ns,vy,vz⟩ :=
    ry.binary_l native hw fa product g j ground
  obtain ⟨_,b,⟨rb,readB⟩,_⟩ := forward z rz
  obtain ⟨p,hp⟩ := g.inhabited
  obtain ⟨j₀,checks,jf,ji⟩ := check_map_l O native g hp
  have same : j₀ = j := funext fun a => (gval_check_map_l O native g hp j₀ checks a (j a)).mp (ground a)
  subst j₀
  have ni : Function.Injective (Subtype.val : (N).Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  obtain ⟨bits,decoded⟩ := readB.binary_decode_l native hM hE Subtype.val ni (smem_full_l I source trans)
    j ji jf (hw.isOrdinal (ZF.modelsKP native)) rb.1 real.1 readY binary decode
  exact ⟨b,rb,bits,decoded,j,ground,y,z,ry,rz,readY,readB,binary,decode,n,C,S,τ,σ,hn,stage,nt,ns,vy,vz⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原规范实数并在背景坍塌中的精确像

名字成员的完整函数图双向对应，在实际背景呈示下成为集合成员方程。
此结论量化给定规范名字的原解释值，不另换泛型或实数族。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hM : M.Models ZF) {c X R : M.Domain}
  (source : Smem_d (kp_pair_l (ZF.modelsKP hM)) c X R) (trans : M.TransitiveSet X)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1).Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "N" => smdl_structure_l I (R := R) (And.left (And.right (And.left source)))
include trans

theorem Rp_name_d.background_image_l {ω A P T U σ : (N).Domain} {H : M.Domain}
    (hw : (N).IsOmega ω) (fa : (N).IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) A ω U)
    (product : Fp_product_d native ω A P T) (generic : Gset_d P.val T.val P.val X H)
    (name : Rp_name_d native ω A P σ)
    {Z : (extension_l N native P T P (fun p => M.mem p.val H)).Domain}
    (value : Qval_d N P T P (fun p => M.mem p.val H) σ Z)
    (e : (extension_l N native P T P (fun p => M.mem p.val H)).Domain → M.Domain)
    (ei : Function.Injective e)
    (ef : ∀ a y, M.mem y (e a) ↔ ∃ b, (extension_l N native P T P (fun p => M.mem p.val H)).mem b a ∧ e b = y)
    (fixed : ∀ a y, Gval_d N P T P (fun p => M.mem p.val H) a y → e y = a.val) :
    ∀ x, M.mem x (e Z) ↔ Rp_bg_d hM source native ω A T H x := by
  let G : (N).Domain → Prop := fun p => M.mem p.val H
  let E := extension_l N native P T P G
  have g := ((source.generic_code_l I hM.1 trans (ZF.modelsKP native) P T P H).mp generic).2
  have hE : E.Models ZF := preserves_zf_l (product.order_l native) native g
  obtain ⟨Z',value',members⟩ := name.value_l native hw fa product g
  have eq : Z' = Z := qval_unique_l value' value
  subst Z'
  obtain ⟨j,ground,forward,backward⟩ := rp_background_l hM source trans native hw fa product generic
  have readEq {y : E.Domain} {x : M.Domain} (fy : Fn0_d (j ω) (j ω) y)
      (fx : Rp_bg_d hM source native ω A T H x) (read : Fn_read_d Subtype.val j y x) : e y = x :=
    read.image_eq_l (ZF.modelsKP hM) (ZF.modelsKP hE) e ei ef (smem_full_l I source trans)
      (fun a => fixed a (j a) (ground a)) fy (fn0_function_l (ZF.modelsKP hM) fx.1).1.1
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy,ey⟩ := (ef Z x).mp hx
    obtain ⟨fy,z,⟨fz,read⟩,_⟩ := forward y ((members y).mp hy)
    exact ((readEq fy fz read).symm.trans ey) ▸ fz
  · intro hx
    obtain ⟨y,⟨fy,read⟩,_⟩ := backward x hx
    exact (ef Z x).mpr ⟨y,(members y).mpr fy,readEq (forward y fy).1 hx read⟩

end YesMetaZFC.Model.Forcing.Internal
