import YesMetaZFC.Model.Forcing.Functions.Coordinate
import YesMetaZFC.Model.Forcing.Collapse.PartialFunctionCertificate
import YesMetaZFC.Model.Forcing.Reflection.Criterion
import YesMetaZFC.Model.Forcing.Collapse.ProductCoordinates
import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable
import YesMetaZFC.Model.Forcing.Collapse.KripkeGeneric
import YesMetaZFC.Model.Forcing.Collapse.ProductReflection
import YesMetaZFC.Model.Forcing.Ground.CheckPool

/-! # 条件坐标的满射坍缩证书

指定行沿加强增长，且每个输入和输出都能由真实加强覆盖。
泛型坐标并图给出满射，有限参数反射给出原偏序上的存在式力迫。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

structure Csurj_d (B R z i X Y : M.Domain) : Prop where
  blocks : ∀ p, M.mem p B → M.IsSetFunction I p
  rows : ∀ p, M.mem p B → ∃ s, Entry_d M i s p
  function : ∀ p, M.mem p B → ∀ s, Entry_d M i s p → Pfn_d I X Y s
  order : ∀ p q, Entry_d M p q R → ∀ s t, Entry_d M i s p → Entry_d M i t q → M.MemberSubset t s
  input : ∀ x, M.mem x X → ∀ p, M.mem p B → p ≠ z →
    ∃ q, Below_d M B R z q p ∧ ∃ s y, Entry_d M i s q ∧ Entry_d M x y s
  output : ∀ y, M.mem y Y → ∀ p, M.mem p B → p ≠ z →
    ∃ q, Below_d M B R z q p ∧ ∃ s x, Entry_d M i s q ∧ Entry_d M x y s

def csurj_m {n} (B R z i X Y : Term n) : Formula 1 n := set[n] ⟪
  (∀ p ∈ ⌜B⌝ₛ, ⌜Formula.isFunction kpair_convention_l⌝ₚ(p)) ∧
  (∀ p ∈ ⌜B⌝ₛ, ∃ s, ⌜entry_m⌝ₚ(⌜i⌝ₛ,s,p)) ∧
  (∀ p ∈ ⌜B⌝ₛ, ∀ s, ⌜entry_m⌝ₚ(⌜i⌝ₛ,s,p) → ⌜pfn_m kpair_convention_l⌝ₚ(⌜X⌝ₛ,⌜Y⌝ₛ,s)) ∧
  (∀ p q, ⌜entry_m⌝ₚ(p,q,⌜R⌝ₛ) → ∀ s t, ⌜entry_m⌝ₚ(⌜i⌝ₛ,s,p) → ⌜entry_m⌝ₚ(⌜i⌝ₛ,t,q) → t ⊆ s) ∧
  (∀ x ∈ ⌜X⌝ₛ, ∀ p ∈ ⌜B⌝ₛ, p ≠ ⌜z⌝ₛ →
    ∃ q, ⌜below_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,q,p) ∧ (∃ s y, ⌜entry_m⌝ₚ(⌜i⌝ₛ,s,q) ∧ ⌜entry_m⌝ₚ(x,y,s))) ∧
  (∀ y ∈ ⌜Y⌝ₛ, ∀ p ∈ ⌜B⌝ₛ, p ≠ ⌜z⌝ₛ →
    ∃ q, ⌜below_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,q,p) ∧ (∃ s x, ⌜entry_m⌝ₚ(⌜i⌝ₛ,s,q) ∧ ⌜entry_m⌝ₚ(x,y,s)))⟫
derive_free_closed csurj_m

theorem csurj_sat_l {n} (ρ : Env M n) (B R z i X Y : Term n) :
    Formula.satisfies ρ (csurj_m B R z i X Y) ↔
      Csurj_d hZF (B.eval ρ) (R.eval ρ) (z.eval ρ) (i.eval ρ) (X.eval ρ) (Y.eval ρ) := by
  simp only [csurj_m,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_isFunction_iff I hZF.1,pfn_sat_l I hZF.1,Formula.satisfies_imp_iff,
    entry_sat_l M hZF.1,Formula.satisfies_subset_iff,Formula.extensionalNe,Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_exists_iff,below_sat_l M hZF.1,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e,f⟩ => ⟨a,b,c,d,e,f⟩,
    fun h => ⟨h.blocks,h.rows,h.function,h.order,h.input,h.output⟩⟩

theorem Csurj_d.value_l {B R z i X Y : M.Domain} (h : Csurj_d hZF B R z i X Y)
    (O : Cond_order_d M B R z) {G : M.Domain → Prop} (generic : Generic_d M B R z G) {b} (hb : G b)
    (j : M.Domain → (extension_l M hZF B R z G).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF B R z G).mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M B R z G t (j a)) :
    let E := extension_l M hZF B R z G
    let J := kpair_interpretation_l E (extension_ext_l O hZF generic) (internal_pair_l O hZF generic)
    ∃ f, E.IsSetFunctionFromTo J f (j X) (j Y) ∧ E.IsSetSurjectiveOnto J f (j X) (j Y) := by
  have input x (hx : M.mem x X) : ∃ p, G p ∧ ∃ s y, Entry_d M i s p ∧ Entry_d M x y s := by
    let φ : UnarySchema 2 := { body := .existsE (.existsE (.conj
      (entry_m (.bound 3) (.bound 1) (.bound 2)) (entry_m (.bound 4) .newest (.bound 1)))) }
    let ρ : Env M 2 := ⟨fun a => [i,x].get a,fun _ => x⟩
    have sat p : φ.denote ρ p ↔ ∃ s y, Entry_d M i s p ∧ Entry_d M x y s := by
      simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,entry_sat_l M hZF.1]; rfl
    exact generic_pick_l hZF generic ⟨2,φ,ρ,sat⟩ hb (fun p hp => h.input x hx p hp.1 hp.2.1)
  obtain ⟨f,fn,graph⟩ := generic_coordinate_l hZF O generic hb
    (fun p hp => h.blocks p (generic.proper p hp).1) (fun p hp => h.rows p (generic.proper p hp).1)
    (fun p hp => h.function p (generic.proper p hp).1) h.order input j inj full checks
  refine ⟨f,fn,fun y hy => ?_⟩
  obtain ⟨a,ha,rfl⟩ := (full Y y).mp hy
  let φ : UnarySchema 2 := { body := .existsE (.existsE (.conj
    (entry_m (.bound 3) (.bound 1) (.bound 2)) (entry_m .newest (.bound 4) (.bound 1)))) }
  let ρ : Env M 2 := ⟨fun k => [i,a].get k,fun _ => a⟩
  have sat p : φ.denote ρ p ↔ ∃ s x, Entry_d M i s p ∧ Entry_d M x a s := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,entry_sat_l M hZF.1]; rfl
  obtain ⟨p,hp,s,x,is,xa⟩ := generic_pick_l hZF generic ⟨2,φ,ρ,sat⟩ hb
    (fun p hp => h.output a ha p hp.1 hp.2.1)
  exact ⟨j x,(image_member_l j inj full).mpr ((h.function p (generic.proper p hp).1 s is).2 x a xa).1,
    (graph (j x) (j a)).mpr ⟨p,hp,s,x,a,is,xa,rfl,rfl⟩⟩

theorem Csurj_d.collapse_l {B R z i X Y a : M.Domain} (h : Csurj_d hZF B R z i X Y)
    (O : Cond_order_d M B R z) (ha : M.mem a B) (nz : a ≠ z) : Collapses_d B R z a X Y := by
  obtain ⟨T,hT,nT,_⟩ := zf_check_l M hZF ha X
  obtain ⟨w,hw,nw,_⟩ := zf_check_l M hZF ha Y
  let φ : Formula 1 2 := .existsE coll_surj_s.body
  let α : Formula 1 9 := .conj (csurj_m (.bound 0) (.bound 1) (.bound 2) (.bound 8) (.bound 3) (.bound 4))
    (.conj (check_m (.bound 5) (.bound 3) (.bound 6)) (check_m (.bound 5) (.bound 4) (.bound 7)))
  have hα : α.FreeClosed := by simp -implicitDefEqProofs [α,Definitional.Formula.FreeClosed]
  have raw (N : Structure.{u}) (hN : N.Models ZF) (η : Env N 9) : Formula.satisfies η α ↔
      Csurj_d hN (η.bound 0) (η.bound 1) (η.bound 2) (η.bound 8) (η.bound 3) (η.bound 4) ∧
      Check_d N (η.bound 5) (η.bound 3) (η.bound 6) ∧ Check_d N (η.bound 5) (η.bound 4) (η.bound 7) := by
    simp only [α,Formula.satisfies_conj_iff,csurj_sat_l hN,check_sat_l N hN.1]; rfl
  let ρ : Env M 9 := ⟨fun k => [B,R,z,X,Y,a,T,w,i].get k,fun _ => w⟩
  let e : Fin 2 → Term 9 := Fin.cases (.bound 6) (fun _ => .bound 7)
  have names : ∀ k, Name_d M B ((e k).eval ρ) := Fin.cases nT (fun _ => nw)
  have force := forces_of_generics_l φ coll_surj_s.freeClosed α hα e (.bound 0) (.bound 1) (.bound 2) (.bound 5)
    (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl rfl (fun N hN η L _ _ _ hraw G generic accepted ξ values => by
      obtain ⟨h,checkT,checkW⟩ := (raw N hN η).mp hraw
      obtain ⟨j,checks,full,inj⟩ := check_map_l L hN generic accepted
      obtain ⟨f,fn,onto⟩ := h.value_l hN L generic accepted j inj full checks
      have eqT := qval_unique_l (checks _ _ checkT) (values 0)
      have eqW := qval_unique_l (checks _ _ checkW) (values 1)
      apply (Formula.satisfies_exists_iff ξ coll_surj_s.body).mpr
      refine ⟨f,(Formula.satisfies_conj_iff (ξ.push f) fn_body_m onto_body_m).mpr ⟨?_,?_⟩⟩
      · exact (Formula.satisfies_isFunctionFromTo_iff _ (extension_ext_l L hN generic) (ξ.push f) .newest (.bound 1) (.bound 2)).mpr
          (eqT ▸ eqW ▸ fn)
      · exact (Formula.satisfies_isSurjectiveOnto_iff _ (ξ.push f) .newest (.bound 1) (.bound 2)).mpr (eqT ▸ eqW ▸ onto))
    hZF ρ O names ha nz ((raw M hZF ρ).mpr ⟨h,hT,hw⟩)
  let σ : Env M 2 := ⟨Fin.cases T (fun _ => w),fun _ => w⟩
  have force' := (forces_env_l (B := B) (R := R) (z := z) hZF.1 φ coll_surj_s.freeClosed
    ⟨fun k => (e k).eval ρ,ρ.free⟩ σ (Fin.cases rfl (fun _ => rfl)) a).mp force
  exact ⟨a,T,w,ha,O.refl a ha,hT,hw,force'⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 有限前缀的大小界与实际坍缩证书

前缀嵌入两层有限序列空间，因而受最大字母表的无限基数约束。
末坐标的真实加强保留全部旧行，给出原前缀偏序自身的坍缩证书。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Fp_prefix_d.bound_l {ω A n C S κ : M.Domain} (stage : Fp_prefix_d hZF ω A n C S)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (hκ : M.IsInfiniteCardinal I ω κ)
    (bound : ∀ i α, M.mem i n → Entry_d M i α A → M.MemberSubset α κ) :
    M.CardinalLessOrEqual I C κ := by
  obtain ⟨V,rows⟩ := ZF.fseq_space_exists_l I hZF hw κ
  obtain ⟨W,blocks⟩ := ZF.fseq_space_exists_l I hZF hw V
  have sub : M.MemberSubset C W := by
    intro p hp
    have fp := (stage.conditions p).mp hp
    refine (blocks p).mpr ⟨n,hn,fp.function,fp.domain,?_⟩
    intro i hi
    obtain ⟨s,is⟩ := (fp.domain i).mp hi
    obtain ⟨α,m,ia,hm,fs⟩ := fp.coordinates i s is
    refine ⟨s,(rows s).mpr ⟨m,hm,fs.1,fs.2.1,?_⟩,is⟩
    intro j hj
    obtain ⟨x,hx,jx⟩ := fs.2.2 j hj
    exact ⟨x,bound i α hi ia x hx,jx⟩
  have id := ZF.exists_inclusionInjection hZF I (fun (x : M.Domain) (hx : M.mem x κ) => hx)
  obtain ⟨f,hf⟩ := ZF.exists_inclusionInjection hZF I sub
  obtain ⟨g,hg⟩ := ZF.fseq_bound_l I hZF hw hκ (ZF.fseq_bound_l I hZF hw hκ id rows) blocks
  exact ZF.exists_compositionInjection hZF I hf hg

theorem Fp_prefix_d.last_certificate_l {ω A n m C S κ : M.Domain} (stage : Fp_prefix_d hZF ω A m C S)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (hm : M.mem m ω) (succ : M.SuccessorOf m n)
    (fa : M.IsSetFunction I A) (alphabet : Entry_d M n κ A) (inh : ∃ x, M.mem x κ) :
    Csurj_d hZF C S C n ω κ := by
  obtain ⟨B,R,space,_,order⟩ := fseq_collapse_order_l hZF hw κ
  have row p (hp : M.mem p C) s (ns : Entry_d M n s p) : M.mem s B := by
    obtain ⟨α,k,na,hk,fs⟩ := ((stage.conditions p).mp hp).coordinates n s ns
    have eq := fa.2 n α κ na alphabet
    subst α
    exact (space s).mpr ⟨k,hk,fs⟩
  have extend p (hp : M.mem p C) s (ns : Entry_d M n s p) t (ht : M.mem t B)
      (st : M.MemberSubset s t) : ∃ q, Below_d M C S C q p ∧ Entry_d M n t q := by
    have fp := (stage.conditions p).mp hp
    obtain ⟨q,s',fq,_,end₀⟩ := fp.split_l hZF hw hn hm succ fa alphabet space
    have ns' := (end₀.entries_l I hZF.1 fq.domain n s').mpr (Or.inr ⟨rfl,rfl⟩)
    have eq := fp.function.2 n s' s ns' ns
    subst s'
    obtain ⟨r,fr,end₁⟩ := fq.snoc_l hZF hw hn succ alphabet ((space t).mp ht)
    have hr := (stage.conditions r).mpr fr
    refine ⟨r,⟨hr,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ hr),
      (stage.order r p).mpr ⟨hr,hp,?_⟩⟩,?_⟩
    · exact (fp_snoc_order_l hZF fq.domain fq.domain end₁ end₀).mpr ⟨Fp_le_d.refl_l I q,st⟩
    · exact (end₁.entries_l I hZF.1 fq.domain n t).mpr (Or.inr ⟨rfl,rfl⟩)
  refine ⟨fun p hp => ((stage.conditions p).mp hp).function,
    fun p hp => (((stage.conditions p).mp hp).domain n).mp succ.predecessor_mem,?_,?_,?_,?_⟩
  · intro p hp s ns
    obtain ⟨k,hk,fs⟩ := (space s).mp (row p hp s ns)
    exact ⟨fs.1,fun a x ax => ⟨hw.transitive (ZF.modelsKP hZF) k hk a (fs.input_mem_of_pairMember ax),
      fs.output_mem_of_pairMember ax⟩⟩
  · intro p q pq s t ns nt
    obtain ⟨r,nr,tr⟩ := ((stage.order p q).mp pq).2.2 n t nt
    have eq := ((stage.conditions p).mp ((stage.order p q).mp pq).1).function.2 n r s nr ns
    exact eq ▸ tr
  · intro a ha p hp _
    obtain ⟨s,ns⟩ := (((stage.conditions p).mp hp).domain n).mp succ.predecessor_mem
    obtain ⟨t,ts,x,ax⟩ := fseq_input_extend_l hZF hw space order inh ha (row p hp s ns)
    obtain ⟨q,qp,nt⟩ := extend p hp s ns t ts.1 ((order t s).mp ts.2.2).2.2
    exact ⟨q,qp,t,x,nt,ax⟩
  · intro x hx p hp _
    obtain ⟨s,ns⟩ := (((stage.conditions p).mp hp).domain n).mp succ.predecessor_mem
    obtain ⟨t,ts,a,ax⟩ := fseq_output_extend_l hZF hw space order hx (row p hp s ns)
    obtain ⟨q,qp,nt⟩ := extend p hp s ns t ts.1 ((order t s).mp ts.2.2).2.2
    exact ⟨q,qp,t,a,nt,ax⟩

theorem Fp_prefix_d.collapses_l {ω A n m C S κ a : M.Domain} (stage : Fp_prefix_d hZF ω A m C S)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (hm : M.mem m ω) (succ : M.SuccessorOf m n)
    (fa : M.IsSetFunction I A) (alphabet : Entry_d M n κ A) (inh : ∃ x, M.mem x κ)
    (ha : M.mem a C) : Collapses_d C S C a ω κ :=
  (stage.last_certificate_l hZF hw hn hm succ fa alphabet inh).collapse_l hZF (stage.order_l hZF) ha
    (fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ ha))

end YesMetaZFC.Model.Forcing.Internal

/-! ## 有限前缀与指定小坍缩的实际泛型比较

在原前缀泛型接受的条件以下使用 Kripke 稠密图。源条件域与关系取调用方
已有的小坍缩，回拉同一个前缀泛型，得到保持全部地参数的扩张同构。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem Fp_prefix_d.comparison_l {ω A n m C S κ Q T : M.Domain}
    (stage : Fp_prefix_d hZF ω A m C S)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (hm : M.mem m ω) (succ : M.SuccessorOf m n)
    (fa : M.IsSetFunction I A) (alphabet : Entry_d M n κ A)
    (hκ : M.IsUncountableCardinal I ω κ)
    (bound : ∀ i α, M.mem i m → Entry_d M i α A → M.MemberSubset α κ)
    (space : Fseq_space_d I ω κ Q) (L : Cond_order_d M Q T Q)
    (order : ∀ p q, Entry_d M p q T ↔ M.mem p Q ∧ M.mem q Q ∧ M.MemberSubset q p)
    {H : M.Domain → Prop} (generic : Generic_d M C S C H) :
    ∃ a Γ, H a ∧ Dmap_at_d Q T Q C S C Γ a ∧
      Generic_d M Q T Q (Pull_generic_d M Γ H) ∧
      Miso_over_d (extension_l M hZF Q T Q (Pull_generic_d M Γ H)) (extension_l M hZF C S C H)
        (Gval_d M Q T Q (Pull_generic_d M Γ H)) (Gval_d M C S C H) := by
  have O := stage.order_l hZF
  have infinite : M.IsInfiniteCardinal I ω κ :=
    ⟨hκ.1,ZF.exists_inclusionInjection hZF I (hκ.1.1.transitive ω hκ.2)⟩
  have size := stage.bound_l hZF hw hm infinite bound
  obtain ⟨a,ha⟩ := generic.inhabited
  have pos := generic.proper a ha
  have collapse := stage.collapses_l hZF hw hn hm succ fa alphabet ⟨ω,hκ.2⟩ pos.1
  obtain ⟨Γ,map,pulled,iso⟩ := kripke_generic_l hZFC O hw hκ size space L order generic ha collapse
  exact ⟨a,Γ,ha,map,pulled,iso⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 从背景滤子列构造 7.23 所需的实际小泛型集合

有限前缀的稠密比较图属于原模型。沿该图回拉逐坐标接受条件，
在背景条件域上直接分离小泛型；同构使用这一个实际集合。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {N : Structure.{u}} {M : Structure.{v}} (hN : N.Models ZFC) (hM : M.Models ZF)
local notation "hZF" => ZFC.models_zf_l hN
local notation "I" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hZF))
local notation "J" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
variable (k : N.Domain → M.Domain) (ki : Function.Injective k)
  (kf : ∀ a y, M.mem y (k a) ↔ ∃ x, N.mem x a ∧ k x = y)
variable {ω A n m C S κ Q T : N.Domain} {F : M.Domain}
local notation "H" => (fun q : N.Domain => N.mem q C ∧ Fp_ready_d J (k m) F (k q))
include ki kf

theorem fp_ground_comparison_l (stage : Fp_prefix_d hZF ω A m C S)
    (hw : N.IsOmega ω) (hn : N.mem n ω) (hm : N.mem m ω) (succ : N.SuccessorOf m n)
    (fa : N.IsSetFunction I A) (alphabet : Entry_d N n κ A) (hκ : N.IsUncountableCardinal I ω κ)
    (bound : ∀ i α, N.mem i m → Entry_d N i α A → N.MemberSubset α κ)
    (space : Fseq_space_d I ω κ Q) (L : Cond_order_d N Q T Q)
    (order : ∀ p q, Entry_d N p q T ↔ N.mem p Q ∧ N.mem q Q ∧ N.MemberSubset q p)
    (generic : Generic_d N C S C H) :
    ∃ a Γ K, H a ∧ Dmap_at_d Q T Q C S C Γ a ∧ M.MemberSubset K (k Q) ∧
      (∀ p, M.mem (k p) K ↔ Pull_generic_d N Γ H p) ∧
      Generic_d N Q T Q (fun p => M.mem (k p) K) ∧
      Miso_over_d (extension_l N hZF Q T Q (fun p => M.mem (k p) K)) (extension_l N hZF C S C H)
        (Gval_d N Q T Q (fun p => M.mem (k p) K)) (Gval_d N C S C H) := by
  obtain ⟨a,Γ,ha,reg,small,iso⟩ := stage.comparison_l hN hw hn hm succ fa alphabet hκ bound space L order generic
  let ρ : Env M 3 := ⟨fun i => [k Γ,k m,F].get i,fun _ => F⟩
  let φ : UnarySchema 3 := { body := .existsE (.conj
    (entry_m (.bound 1) .newest (.bound 2))
    (fp_ready_m (𝒞 := kpair_convention_l) (.bound 3) (.bound 4) .newest)) }
  have sat p : φ.denote ρ p ↔ ∃ q, Entry_d M p q (k Γ) ∧ Fp_ready_d J (k m) F q := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      entry_sat_l M hM.1,fp_ready_sat_l J]
    rfl
  obtain ⟨K,members⟩ := ZF.separation_exists_d hM φ ρ (k Q)
  have read p : M.mem (k p) K ↔ Pull_generic_d N Γ H p := by
    apply ((members (k p)).trans (and_congr_right fun _ => sat (k p))).trans
    constructor
    · rintro ⟨_,q,⟨v,pair,vg⟩,ready⟩
      obtain ⟨w,wg,eq⟩ := (kf Γ v).mp vg
      have pair' := eq.symm ▸ pair
      obtain ⟨a,b,ab,ap,bq⟩ := image_kpair_pull_l (ZF.modelsKP hZF) hM.1 k ki kf pair'
      have eq := ki ap
      subst a
      have pb : Entry_d N p b Γ := ⟨w,ab,wg⟩
      exact ⟨b,pb,(reg.domain p b pb).2.2.1,bq.symm ▸ ready⟩
    · rintro ⟨q,pq,hq,ready⟩
      exact ⟨(image_member_l k ki kf).mpr (reg.domain p q pq).1,k q,
        (image_entry_iff_l k ki kf (KP.exists_pair (ZF.modelsKP hZF)) hM.1 p q Γ).mp pq,ready⟩
  have same : Pull_generic_d N Γ H = (fun p => M.mem (k p) K) := by
    funext p
    exact propext (read p).symm
  exact ⟨a,Γ,K,ha,reg,fun p hp => ((members p).mp hp).1,read,same ▸ small,same ▸ iso⟩

end YesMetaZFC.Model.Forcing.Internal
