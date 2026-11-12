import YesMetaZFC.Model.Forcing.Functions.Surjection
import YesMetaZFC.Model.Forcing.Functions.Generic
import YesMetaZFC.Model.Forcing.Reflection.Criterion

/-! # “旧集合被迫可数”的通常存在式入口

最大值原理提供具体满射名字；调用方不需提供判值反链或树工厂。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def coll_surj_s : UnarySchema 2 where
  body := .conj fn_body_m onto_body_m
  freeClosed := ⟨fn_body_closed_l,onto_body_closed_l⟩

def Collapses_d (B R z a ω κ : M.Domain) : Prop := ∃ b T w,
  M.mem b B ∧ Entry_d M a b R ∧ Check_d M b ω T ∧ Check_d M b κ w ∧
    Forces_d M B R z (.existsE coll_surj_s.body) ⟨Fin.cases T (fun _ => w),fun _ => w⟩ a

theorem Collapses_d.name_l (hZFC : M.Models ZFC) {B R z a ω κ : M.Domain} (O : Cond_order_d M B R z)
    (ha : M.mem a B) (hz : a ≠ z) (collapse : Collapses_d B R z a ω κ) : ∃ b T w f,
      M.mem b B ∧ Below_d M B R z a b ∧ Check_d M b ω T ∧ Check_d M b κ w ∧ Onto_name_d B R z a T w f := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨b,T,w,hb,ab,hT,hw,existsF⟩ := collapse
  have nT := check_name_l M (check_range_l M hZF) hb hT
  have nw := check_name_l M (check_range_l M hZF) hb hw
  let ρ : Env M 2 := ⟨Fin.cases T (fun _ => w),fun _ => w⟩
  obtain ⟨f,nf,_,maximum⟩ := maximum_l O hZFC coll_surj_s ρ (Fin.cases nT (fun _ => nw))
  have same : ∀ i, (ρ.push f).bound i = (fn_env_l T w f).bound i :=
    Fin.cases rfl (Fin.cases rfl (fun _ => rfl))
  have force := (forces_env_l hZF.1 coll_surj_s.body coll_surj_s.freeClosed (ρ.push f) (fn_env_l T w f) same a).mp
    ((maximum a ha hz).mp existsF)
  obtain ⟨function,onto⟩ := (forces_conj_l fn_body_m onto_body_m (fn_env_l T w f) a).mp force
  exact ⟨b,T,w,f,hb,⟨ha,hz,ab⟩,hT,hw,⟨nT,nw,nf,function⟩,onto⟩

theorem Onto_name_d.collapse_l (hZF : M.Models ZF) {B R z a b T w f ω κ : M.Domain} (O : Cond_order_d M B R z)
    (name : Onto_name_d B R z a T w f) (hb : M.mem b B) (ha : Below_d M B R z a b)
    (hT : Check_d M b ω T) (hw : Check_d M b κ w) : Collapses_d B R z a ω κ := by
  let ρ : Env M 2 := ⟨Fin.cases T (fun _ => w),fun _ => w⟩
  have names : ∀ v : Term 3, Name_d M B (v.eval (ρ.push f)) := by
    intro v; cases v with
    | free _ => exact name.1.2.1
    | bound i => exact Fin.cases name.1.2.2.1 (Fin.cases name.1.1 (fun _ => name.1.2.1)) i
  have same : ∀ i, (ρ.push f).bound i = (fn_env_l T w f).bound i :=
    Fin.cases rfl (Fin.cases rfl (fun _ => rfl))
  have force : Forces_d M B R z coll_surj_s.body (ρ.push f) a :=
    (forces_env_l hZF.1 coll_surj_s.body coll_surj_s.freeClosed (ρ.push f) (fn_env_l T w f) same a).mpr
      ((forces_conj_l fn_body_m onto_body_m (fn_env_l T w f) a).mpr ⟨name.1.2.2.2,name.2⟩)
  exact ⟨b,T,w,hb,ha.2.2,hT,hw,forces_exists_intro_l O hZF.1 name.1.2.2.1
    (forces_regular_l O hZF coll_surj_s.body (ρ.push f) names).1 ha.1 force⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 部分函数条件的满射坍缩证书

条件图单调增长，且每个源坐标、每个目标值都可由加强覆盖，则泛型并图为满射。
有限参数反射把这一真实名字的泛型读取升回每个条件上的存在式力迫。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

structure Psurj_d (B R z X Y : M.Domain) : Prop where
  function : ∀ p, M.mem p B → Pfn_d I X Y p
  order : ∀ p q, Entry_d M p q R → M.MemberSubset q p
  input : ∀ x, M.mem x X → ∀ p, M.mem p B → p ≠ z → ∃ q, Below_d M B R z q p ∧ ∃ y, Entry_d M x y q
  output : ∀ y, M.mem y Y → ∀ p, M.mem p B → p ≠ z → ∃ q, Below_d M B R z q p ∧ ∃ x, Entry_d M x y q

def psurj_m {n} (B R z X Y : Term n) : Formula 1 n := set[n] ⟪
  (∀ p ∈ ⌜B⌝ₛ, ⌜(pfn_m kpair_convention_l)⌝ₚ(⌜X⌝ₛ,⌜Y⌝ₛ,p)) ∧
  (∀ p, ∀ q, ⌜entry_m⌝ₚ(p,q,⌜R⌝ₛ) → q ⊆ p) ∧
  (∀ x ∈ ⌜X⌝ₛ, ∀ p ∈ ⌜B⌝ₛ, p ≠ ⌜z⌝ₛ →
    ∃ q, ⌜below_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,q,p) ∧ (∃ y, ⌜entry_m⌝ₚ(x,y,q))) ∧
  (∀ y ∈ ⌜Y⌝ₛ, ∀ p ∈ ⌜B⌝ₛ, p ≠ ⌜z⌝ₛ →
    ∃ q, ⌜below_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,q,p) ∧ (∃ x, ⌜entry_m⌝ₚ(x,y,q)))⟫
derive_free_closed psurj_m

theorem psurj_sat_l {n} (ρ : Env M n) (B R z X Y : Term n) :
    Formula.satisfies ρ (psurj_m B R z X Y) ↔ Psurj_d hZF (B.eval ρ) (R.eval ρ) (z.eval ρ) (X.eval ρ) (Y.eval ρ) := by
  simp only [psurj_m,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,
    pfn_sat_l I hZF.1,Formula.satisfies_imp_iff,entry_sat_l M hZF.1,Formula.satisfies_subset_iff,
    Formula.extensionalNe,Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_exists_iff,below_sat_l M hZF.1,Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,fun h => ⟨h.function,h.order,h.input,h.output⟩⟩

theorem Psurj_d.value_l {B R z X Y : M.Domain} (h : Psurj_d hZF B R z X Y) (O : Cond_order_d M B R z)
    {G : M.Domain → Prop} (generic : Generic_d M B R z G) {b} (hb : G b)
    (j : M.Domain → (extension_l M hZF B R z G).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF B R z G).mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M B R z G t (j a)) :
    let E := extension_l M hZF B R z G
    let J := kpair_interpretation_l E (extension_ext_l O hZF generic) (internal_pair_l O hZF generic)
    ∃ f, E.IsSetFunctionFromTo J f (j X) (j Y) ∧ E.IsSetSurjectiveOnto J f (j X) (j Y) := by
  have input x (hx : M.mem x X) : ∃ p, G p ∧ ∃ y, Entry_d M x y p := by
    let φ : UnarySchema 1 := { body := .existsE (entry_m (.bound 2) .newest (.bound 1)) }
    let ρ : Env M 1 := ⟨fun _ => x,fun _ => x⟩
    have sat p : φ.denote ρ p ↔ ∃ y, Entry_d M x y p := by
      simp only [UnarySchema.denote,φ,Formula.satisfies_exists_iff,entry_sat_l M hZF.1]; rfl
    exact generic_pick_l hZF generic ⟨1,φ,ρ,sat⟩ hb (fun p hp => h.input x hx p hp.1 hp.2.1)
  obtain ⟨f,fn,graph⟩ := generic_function_l (hEN := extension_ext_l O hZF generic) (hPN := internal_pair_l O hZF generic)
    O hZF generic hb (fun {p} hp => h.function p (generic.proper p hp).1) h.order input j inj full checks
  refine ⟨f,fn,fun y hy => ?_⟩
  obtain ⟨a,ha,rfl⟩ := (full Y y).mp hy
  let φ : UnarySchema 1 := { body := .existsE (entry_m .newest (.bound 2) (.bound 1)) }
  let ρ : Env M 1 := ⟨fun _ => a,fun _ => a⟩
  have sat p : φ.denote ρ p ↔ ∃ x, Entry_d M x a p := by
    simp only [UnarySchema.denote,φ,Formula.satisfies_exists_iff,entry_sat_l M hZF.1]; rfl
  obtain ⟨p,hp,x,xa⟩ := generic_pick_l hZF generic ⟨1,φ,ρ,sat⟩ hb (fun p hp => h.output a ha p hp.1 hp.2.1)
  exact ⟨j x,(image_member_l j inj full).mpr ((h.function p (generic.proper p hp).1).2 x a xa).1,
    (graph (j x) (j a)).mpr ⟨p,hp,x,a,xa,rfl,rfl⟩⟩

theorem Psurj_d.collapse_l {B R z X Y a : M.Domain} (h : Psurj_d hZF B R z X Y)
    (O : Cond_order_d M B R z) (ha : M.mem a B) (nz : a ≠ z) : Collapses_d B R z a X Y := by
  obtain ⟨T,hT,nT,_⟩ := zf_check_l M hZF ha X
  obtain ⟨w,hw,nw,_⟩ := zf_check_l M hZF ha Y
  let φ : Formula 1 2 := .existsE coll_surj_s.body
  have hφ : φ.FreeClosed := coll_surj_s.freeClosed
  let α : Formula 1 8 := .conj (psurj_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4))
    (.conj (check_m (.bound 5) (.bound 3) (.bound 6)) (check_m (.bound 5) (.bound 4) (.bound 7)))
  have hα : α.FreeClosed := by simp -implicitDefEqProofs [α,Definitional.Formula.FreeClosed]
  have raw (N : Structure.{u}) (hN : N.Models ZF) (η : Env N 8) : Formula.satisfies η α ↔
      Psurj_d hN (η.bound 0) (η.bound 1) (η.bound 2) (η.bound 3) (η.bound 4) ∧
      Check_d N (η.bound 5) (η.bound 3) (η.bound 6) ∧ Check_d N (η.bound 5) (η.bound 4) (η.bound 7) := by
    simp only [α,Formula.satisfies_conj_iff,psurj_sat_l hN,check_sat_l N hN.1]; rfl
  let ρ : Env M 8 := ⟨fun i => [B,R,z,X,Y,a,T,w].get i,fun _ => w⟩
  let e : Fin 2 → Term 8 := Fin.cases (.bound 6) (fun _ => .bound 7)
  have names : ∀ i, Name_d M B ((e i).eval ρ) := Fin.cases nT (fun _ => nw)
  have force := forces_of_generics_l φ hφ α hα e (.bound 0) (.bound 1) (.bound 2) (.bound 5)
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
  have force' := (forces_env_l (B := B) (R := R) (z := z) hZF.1 φ hφ
    ⟨fun i => (e i).eval ρ,ρ.free⟩ σ (Fin.cases rfl (fun _ => rfl)) a).mp force
  exact ⟨a,T,w,ha,O.refl a ha,hT,hw,force'⟩

end YesMetaZFC.Model.Forcing.Internal
