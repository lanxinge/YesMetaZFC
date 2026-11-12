import YesMetaZFC.Model.Forcing.Functions.ValueIsomorphism
import YesMetaZFC.Model.SetTheory.LevyReflection.Decode
import YesMetaZFC.Model.Forcing.Embedding.Rank
import YesMetaZFC.Model.SetTheory.Reflection.ReflectedSeed
import YesMetaZFC.Model.SetTheory.LevyReflection.Arguments

/-! # 实数名字见证的背景公式

所有名字与力迫条件均量化于原传递模型内，滤子和被解释的实数是背景集合。
相对化保留原模型自己的力迫判断，给出可直接用于内部状态分离的单一公式。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u

def fn_check0_m : Formula 1 10 := .conj (check_m (.bound 3) (.bound 4) (.bound 7))
  (.conj (check_m (.bound 3) (.bound 5) (.bound 8))
    (fn_name_m (.bound 0) (.bound 1) (.bound 2) (.bound 6) (.bound 7) (.bound 8) (.bound 9)))
@[simp] theorem fn_check0_closed_l : fn_check0_m.FreeClosed := by
  simp -implicitDefEqProofs [fn_check0_m,Definitional.Formula.FreeClosed]

def nentry0_m : Formula 1 8 := nentry_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)
@[simp] theorem nentry0_closed_l : nentry0_m.FreeClosed := by simp -implicitDefEqProofs [nentry0_m]

/-- 八个参数依次为原载体、条件域、顺序、排除值、函数源、目标、滤子与背景图。 -/
def fn_code0_m : Formula 1 8 :=
  let typed : Formula 1 13 := lr_rel_m fn_check0_m (.bound 5)
    (fun i => .bound (([6,7,8,4,9,10,3,2,1,0] : List (Fin 13)).get i))
  let edge : Formula 1 16 := lr_rel_m nentry0_m (.bound 8)
    (fun i => .bound (([9,10,11,7,3,2,1,0] : List (Fin 16)).get i))
  let rows : Formula 1 13 := .forallE (.forallE (.iff (entry_m (.bound 1) .newest (.bound 14))
    (.conj (.mem (.bound 1) (.bound 7)) (.conj (.mem .newest (.bound 7))
      (Formula.existsMem (.bound 7) (.conj (.mem .newest (.bound 14)) edge))))))
  Formula.existsMem (.bound 0) (Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
    (Formula.existsMem (.bound 3) (Formula.existsMem (.bound 4)
      (.conj (.mem (.bound 4) (.bound 11)) (.conj (.mem (.bound 3) (.bound 11))
        (.conj typed rows)))))))

@[simp] theorem fn_code0_closed_l : fn_code0_m.FreeClosed := by
  simp -implicitDefEqProofs [fn_code0_m,Definitional.Formula.FreeClosed]

def Fn_bg_d {M : Structure.{u}} (X B R z D A H x : M.Domain) : Prop :=
  Formula.satisfies (⟨fun i => [X,B,R,z,D,A,H,x].get i,fun _ => x⟩ : Env M 8) fn_code0_m

def fn_bg_m {d} (X B R z D A H x : Term d) : Formula 1 d :=
  fn_code0_m.bind (fun i => [X,B,R,z,D,A,H,x].get i)

@[simp] theorem fn_bg_closed_l {d} (X B R z D A H x : Term d)
    (hX : X.freeSupport = []) (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hD : D.freeSupport = []) (hA : A.freeSupport = []) (hH : H.freeSupport = []) (hx : x.freeSupport = []) :
    (fn_bg_m X B R z D A H x).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr fn_code0_closed_l
  intro i
  exact Fin.cases hX (Fin.cases hB (Fin.cases hR (Fin.cases hz
    (Fin.cases hD (Fin.cases hA (Fin.cases hH (Fin.cases hx (fun i => Fin.elim0 i)))))))) i

theorem fn_bg_sat_l {M : Structure.{u}} {d} (ρ : Env M d) (X B R z D A H x : Term d) :
    Formula.satisfies ρ (fn_bg_m X B R z D A H x) ↔
      Fn_bg_d (X.eval ρ) (B.eval ρ) (R.eval ρ) (z.eval ρ) (D.eval ρ) (A.eval ρ) (H.eval ρ) (x.eval ρ) := by
  rw [fn_bg_m,Formula.satisfies_bind]
  apply Formula.closed_env_l _ fn_code0_closed_l
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))) i

variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hM : Extensional M)
  {c X R : M.Domain} (source : Smem_d I c X R) (trans : M.TransitiveSet X)
local notation "N" => smdl_structure_l I (R := R) (And.left (And.right (And.left source)))
include hM trans

theorem fn_bg_read_l (hN : Extensional N) (B T z D A : (N).Domain) (H x : M.Domain) :
    Fn_bg_d X B.val T.val z.val D.val A.val H x ↔
      Fn_code_d Subtype.val B T z D A (fun p => M.mem p.val H) x := by
  let ρ : Env M 8 := ⟨fun i => [X,B.val,T.val,z.val,D.val,A.val,H,x].get i,fun _ => x⟩
  have typed (b p t w τ : (N).Domain) :=
    (lr_rel_decode_l I source.1 source.2 trans fn_check0_m fn_check0_closed_l
      (⟨fun i => [B,T,z,b,D,A,p,t,w,τ].get i,fun _ => τ⟩ : Env N 10)
      (((((ρ.push b.val).push p.val).push t.val).push w.val).push τ.val) (.bound 5)
      (fun i => .bound (([6,7,8,4,9,10,3,2,1,0] : List (Fin 13)).get i)) rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))))))).trans
      (show Formula.satisfies (⟨fun i => [B,T,z,b,D,A,p,t,w,τ].get i,fun _ => τ⟩ : Env N 10) fn_check0_m ↔
        Check_d N b D t ∧ Check_d N b A w ∧ Fn_name_d N B T z p t w τ from by
          simp only [fn_check0_m,Formula.satisfies_conj_iff,check_sat_l N hN,fn_name_sat_l hN]; rfl)
  have entry (b p t w τ a d q : (N).Domain) :=
    (lr_rel_decode_l I source.1 source.2 trans nentry0_m nentry0_closed_l
      (⟨fun i => [B,T,z,b,τ,a,d,q].get i,fun _ => τ⟩ : Env N 8)
      ((((((((ρ.push b.val).push p.val).push t.val).push w.val).push τ.val).push a.val).push d.val).push q.val)
      (.bound 8) (fun i => .bound (([9,10,11,7,3,2,1,0] : List (Fin 16)).get i)) rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))))).trans
      (show Formula.satisfies (⟨fun i => [B,T,z,b,τ,a,d,q].get i,fun _ => τ⟩ : Env N 8) nentry0_m ↔
        Nentry_d B T z b τ a d q from by simp only [nentry0_m,nentry_sat_l hN]; rfl)
  change Formula.satisfies ρ fn_code0_m ↔ _
  simp only [fn_code0_m,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,entry_sat_l M hM]
  constructor
  · rintro ⟨b,hb,p,hp,t,ht,w,hw,τ,hτ,bH,pH,fn,read⟩
    let b₀ : (N).Domain := ⟨b,hb⟩
    let p₀ : (N).Domain := ⟨p,hp⟩
    let t₀ : (N).Domain := ⟨t,ht⟩
    let w₀ : (N).Domain := ⟨w,hw⟩
    let τ₀ : (N).Domain := ⟨τ,hτ⟩
    obtain ⟨ct,cw,force⟩ := (typed b₀ p₀ t₀ w₀ τ₀).mp fn
    refine ⟨b₀,p₀,t₀,w₀,τ₀,bH,pH,ct,cw,force,fun i y => ?_⟩
    apply (read i y).trans
    constructor
    · rintro ⟨hi,hy,q,hq,qH,force⟩
      exact ⟨⟨i,hi⟩,⟨y,hy⟩,rfl,rfl,⟨q,hq⟩,qH,(entry b₀ p₀ t₀ w₀ τ₀ ⟨i,hi⟩ ⟨y,hy⟩ ⟨q,hq⟩).mp force⟩
    · rintro ⟨a,d,rfl,rfl,q,qH,force⟩
      exact ⟨a.property,d.property,q.val,q.property,qH,(entry b₀ p₀ t₀ w₀ τ₀ a d q).mpr force⟩
  · rintro ⟨b,p,t,w,τ,bH,pH,ct,cw,fn,read⟩
    refine ⟨b.val,b.property,p.val,p.property,t.val,t.property,w.val,w.property,τ.val,τ.property,
      bH,pH,(typed b p t w τ).mpr ⟨ct,cw,fn⟩,fun i y => ?_⟩
    apply (read i y).trans
    constructor
    · rintro ⟨a,d,rfl,rfl,q,qH,force⟩
      exact ⟨a.property,d.property,q.val,q.property,qH,(entry b p t w τ a d q).mpr force⟩
    · rintro ⟨hi,hy,q,hq,qH,force⟩
      exact ⟨⟨i,hi⟩,⟨y,hy⟩,rfl,rfl,⟨q,hq⟩,qH,(entry b p t w τ ⟨i,hi⟩ ⟨y,hy⟩ ⟨q,hq⟩).mp force⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 初等名字提升保持同一个完整实数图

目标泛型接受旧条件的像，且两侧地模型逐点识别同一个 ω。函数的全定义性
排除额外图边；因此不需要目标条件全有旧原像，也不假设低秩幂集已相同。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u v w
variable {M : Structure.{u}} {N : Structure.{v}} {L : Structure.{w}}

/-- 保留解释名字本身，并把原背景实数的值域识别为同一个 ω。 -/
theorem Fn_code_d.real_value_l (hM : M.Models KP) (hN : N.Models ZF)
    (k : N.Domain → M.Domain) (ki : Function.Injective k)
    (kf : ∀ a y, M.mem y (k a) ↔ ∃ b, N.mem b a ∧ k b = y)
    {ω B R z A : N.Domain} {U : N.Domain → Prop} {x : M.Domain}
    (O : Cond_order_d N B R z) (g : Generic_d N B R z U) (real : Fn0_d (k ω) (k ω) x)
    (code : Fn_code_d k B R z ω A U x) :
    let E := extension_l N hN B R z U
    ∃ τ, ∃ j : N.Domain → E.Domain, ∃ y : E.Domain,
      Qval_d N B R z U τ y ∧ (∀ a, Gval_d N B R z U a (j a)) ∧
        Fn0_d (j ω) (j ω) y ∧ Fn_read_d k j y x := by
  obtain ⟨b,p,t,w,τ,hb,hp,ct,cw,fn,read⟩ := code
  have hE := preserves_zf_l O hN g
  obtain ⟨j,checks,full,inj⟩ := check_map_l O hN g hb
  obtain ⟨y,value⟩ := name_value_l (R := R) (z := z) (U := U) fn.2.2.1
  have fy := fn_name_val_l O hN g fn hp (checks ω t ct) (checks A w cw) value
  have result : Fn_read_d k j y x := fun i c => (read i c).trans
    (exists_congr fun a => exists_congr fun b => and_congr_right fun _ => and_congr_right fun _ =>
      nentry_truth_l hN O g hb value j checks a b)
  exact ⟨τ,j,y,value,fun a => (gval_check_map_l O hN g hb j checks a (j a)).mpr rfl,
    fn0_of_function_l (ZF.modelsKP hE) (result.range_l hM (ZF.modelsKP hE) ki kf inj full fy (fn0_function_l hM real)),result⟩

theorem fn_code_real_lift_l (hM : M.Models KP) (hN : Extensional N) (hL : L.Models ZF)
    (e : N.Domain → L.Domain) (elem : Pe_d e)
    (k : N.Domain → M.Domain) (ki : Function.Injective k)
    (kf : ∀ a y, M.mem y (k a) ↔ ∃ b, N.mem b a ∧ k b = y)
    (l : L.Domain → M.Domain) (li : Function.Injective l)
    (lf : ∀ a y, M.mem y (l a) ↔ ∃ b, L.mem b a ∧ l b = y)
    {ω B R z A : N.Domain} {U : N.Domain → Prop} {V : L.Domain → Prop} {x : M.Domain}
    (fixedω : l (e ω) = k ω) (fixed : ∀ a, N.mem a ω → l (e a) = k a)
    (O : Cond_order_d L (e B) (e R) (e z)) (generic : Generic_d L (e B) (e R) (e z) V)
    (accepted : ∀ p, U p → V (e p)) (real : Fn0_d (k ω) (k ω) x)
    (code : Fn_code_d k B R z ω A U x) : Fn_code_d l (e B) (e R) (e z) (e ω) (e A) V x := by
  obtain ⟨b,p,t,w,τ,hb,hp,ct,cw,fn,read⟩ := code
  let E := extension_l L hL (e B) (e R) (e z) V
  have hE := preserves_zf_l O hL generic
  have typed : Fn_name_d L (e B) (e R) (e z) (e p) (e t) (e w) (e τ) := by
    let ρ : Env N 7 := ⟨fun i => [B,R,z,p,t,w,τ].get i,fun _ => τ⟩
    let φ := fn_name_m (.bound 0 : Term 7) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)
    exact (fn_name_sat_l hL.1 (image_env_l e ρ) _ _ _ _ _ _ _).mp
      ((elem φ (by simp -implicitDefEqProofs [φ]) ρ).mp ((fn_name_sat_l hN ρ _ _ _ _ _ _ _).mpr fn))
  have edge {a c q : N.Domain} (h : Nentry_d B R z b τ a c q) :
      Nentry_d (e B) (e R) (e z) (e b) (e τ) (e a) (e c) (e q) := by
    let ρ : Env N 8 := ⟨fun i => [B,R,z,b,τ,a,c,q].get i,fun _ => τ⟩
    exact (nentry_sat_l hL.1 (image_env_l e ρ) _ _ _ _ _ _ _ _).mp
      ((elem nentry0_m nentry0_closed_l ρ).mp ((nentry_sat_l hN ρ _ _ _ _ _ _ _ _).mpr h))
  obtain ⟨j,checks,full,inj⟩ := check_map_l O hL generic (accepted b hb)
  obtain ⟨y,value⟩ := name_value_l (R := e R) (z := e z) (U := V) typed.2.2.1
  have fnY := fn_name_val_l O hL generic typed (accepted p hp)
    (checks (e ω) (e t) ((em_check_l hN hL.1 e elem).mp ct))
    (checks (e A) (e w) ((em_check_l hN hL.1 e elem).mp cw)) value
  have fx := fn0_function_l hM real
  have fx' : M.IsSetFunctionFromTo (kp_pair_l hM) x (l (e ω)) (k ω) := fixedω.symm ▸ fx
  have rows (a : L.Domain) (ha : L.mem a (e ω)) :
      ∃ c, Entry_d M (l a) (l c) x ∧ Entry_d E (j a) (j c) y := by
    have haM : M.mem (l a) (k ω) := fixedω ▸ (image_member_l l li lf).mpr ha
    obtain ⟨c,hc,ac⟩ := fx.2.2 (l a) haM
    obtain ⟨a₀,c₀,ea,ec,q,hq,force⟩ := (read (l a) c).mp ac
    have ha₀ := (image_member_l k ki kf).mp (ea.symm ▸ haM)
    have hc₀ := (image_member_l k ki kf).mp (ec.symm ▸ hc)
    have eqa : e a₀ = a := li ((fixed a₀ ha₀).trans ea)
    have eqc : l (e c₀) = c := (fixed c₀ hc₀).trans ec
    refine ⟨e c₀,eqc.symm ▸ ac,?_⟩
    have lifted := (nentry_truth_l hL O generic (accepted b hb) value j checks (e a₀) (e c₀)).mp
      ⟨e q,accepted q hq,edge force⟩
    exact eqa ▸ lifted
  have result := (function_read_l hM (ZF.modelsKP hE) l li lf j inj full fx' fnY rows).1
  exact fn_code_of_value_l hL O generic l j
    (fun a => (gval_check_map_l O hL generic (accepted b hb) j checks a (j a)).mpr rfl)
    (fn0_of_function_l (ZF.modelsKP hE) fnY) result

/-- 已回收到地模型的名字，其目标实数解释也由原泛型解释为同一个背景图。 -/
theorem fn_value_real_pull_l (hM : M.Models KP) (hN : N.Models ZF) (hL : L.Models ZF)
    (e : N.Domain → L.Domain) (elem : Pe_d e)
    (k : N.Domain → M.Domain) (ki : Function.Injective k)
    (kf : ∀ a y, M.mem y (k a) ↔ ∃ b, N.mem b a ∧ k b = y)
    (l : L.Domain → M.Domain) (li : Function.Injective l)
    {ω B R z τ : N.Domain} {U : N.Domain → Prop} {V : L.Domain → Prop} {x : M.Domain}
    (fixed : ∀ a, N.mem a ω → l (e a) = k a)
    (O : Cond_order_d N B R z) (gU : Generic_d N B R z U)
    (gV : Generic_d L (e B) (e R) (e z) V) (accepted : ∀ p, U p → V (e p))
    (j : L.Domain → (extension_l L hL (e B) (e R) (e z) V).Domain)
    (ground : ∀ a, Gval_d L (e B) (e R) (e z) V a (j a))
    {y : (extension_l L hL (e B) (e R) (e z) V).Domain}
    (value : Qval_d L (e B) (e R) (e z) V (e τ) y)
    (fn : Fn0_d (j (e ω)) (j (e ω)) y) (read : Fn_read_d l j y x)
    (real : Fn0_d (k ω) (k ω) x) : Fn_value_d hN k B R z ω τ U x := by
  let E := extension_l N hN B R z U
  let D := extension_l L hL (e B) (e R) (e z) V
  have hE := preserves_zf_l O hN gU
  have O' := em_order_l hN.1 hL.1 e elem O
  have hD := preserves_zf_l O' hL gV
  let f : E.Domain → D.Domain := em_lift_l hN.1 hL.1 e elem accepted
  have ef : Pe_d f := em_lift_elementary_l hN hL e elem accepted O gU gV
  obtain ⟨b,hb⟩ := gU.inhabited
  obtain ⟨a,checks,full,inj⟩ := check_map_l O hN gU hb
  have commute s : f (a s) = j (e s) := by
    obtain ⟨t,ct,_⟩ := zf_check_l N hN (gU.proper b hb).1 s
    have vg : Gval_d L (e B) (e R) (e z) V (e s) (f (a s)) :=
      ⟨e b,e t,accepted b hb,(em_check_l hN.1 hL.1 e elem).mp ct,
        em_lift_value_l hN.1 hL.1 e elem accepted (checks s t ct)⟩
    exact vg.unique_l O' hL gV (ground (e s))
  have name := (em_name_l hN.1 hL.1 e elem).mpr (qval_name_l value)
  obtain ⟨y₀,v₀⟩ := name_value_l (R := R) (z := z) (U := U) name
  have eq : f y₀ = y := qval_unique_l (em_lift_value_l hN.1 hL.1 e elem accepted v₀) value
  have fn₀ : Fn0_d (a ω) (a ω) y₀ := by
    let ρ : Env E 3 := ⟨fun i => [a ω,a ω,y₀].get i,fun _ => y₀⟩
    exact (fn0_sat_l hE.1 ρ (.bound 0) (.bound 1) (.bound 2)).mp
      ((ef (fn0_m (.bound 0) (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs) ρ).mpr
        ((fn0_sat_l hD.1 (image_env_l f ρ) (.bound 0) (.bound 1) (.bound 2)).mpr (by
          change Fn0_d (f (a ω)) (f (a ω)) (f y₀)
          simpa only [commute,eq] using fn)))
  have fx := fn0_function_l hM real
  have rows s (hs : N.mem s ω) : ∃ t, Entry_d M (k s) (k t) x ∧ Entry_d E (a s) (a t) y₀ := by
    obtain ⟨v,hv,sv⟩ := fx.2.2 (k s) ((image_member_l k ki kf).mpr hs)
    obtain ⟨t,ht,rfl⟩ := (kf ω v).mp hv
    obtain ⟨s',t',es,et,edge⟩ := (read (k s) (k t)).mp sv
    have es' : s' = e s := li (es.trans (fixed s hs).symm)
    have et' : t' = e t := li (et.trans (fixed t ht).symm)
    refine ⟨t,sv,(em_entry_l hE.1 hD.1 f ef (a s) (a t) y₀).mpr ?_⟩
    simpa only [commute,eq,es',et'] using edge
  have old := (function_read_l hM (ZF.modelsKP hE) k ki kf a inj full fx
    (fn0_function_l (ZF.modelsKP hE) fn₀) rows).1
  exact ⟨a,y₀,v₀,(fun s => (gval_check_map_l O hN gU hb a checks s (a s)).mpr rfl),fn₀,old⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原名字解释的完整背景图留在反射壳内

力迫判断相对化于原载体，图边是旧参数的有界定义。真实图闭包构造
同一关系图，再逐边识别已有背景实数；不要求测试壳满足 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rg_closed_d.real_code_inside_l {P X B T z D A H x : M.Domain}
    (closed : Rg_closed_d I P) (trans : M.TransitiveSet P)
    (hX : M.mem X P) (hB : M.mem B P) (hT : M.mem T P) (hz : M.mem z P) (hH : M.mem H P)
    (code : Fn_bg_d X B T z D A H x) (rel : M.IsSetRelation I x) : M.mem x P := by
  let η : Env M 8 := ⟨fun k => [X,B,T,z,D,A,H,x].get k,fun _ => x⟩
  change Formula.satisfies η fn_code0_m at code
  simp only [fn_code0_m,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,entry_sat_l M hZF.1] at code
  obtain ⟨b,hb,p,_,t,_,w,_,τ,hτ,_,_,_,rows⟩ := code
  let ρ : Env M 7 := ⟨fun k => [X,B,T,z,b,τ,H].get k,fun _ => X⟩
  let φ : Delta0BinarySchema 7 := {
    body := Formula.existsMem (.bound 2) (.conj (.mem .newest (.bound 9))
      (lr_rel_m nentry0_m (.bound 3) (fun i => .bound (([4,5,6,7,8,2,1,0] : List (Fin 10)).get i))))
    freeClosed := by
      simp only [Formula.existsMem,Definitional.Formula.FreeClosed]
      exact ⟨⟨rfl,rfl⟩,⟨⟨rfl,rfl⟩,lr_rel_closed_l _ nentry0_closed_l _ _ rfl (fun _ => rfl)⟩⟩
    delta0 := .existsMem _ (.conj (.mem _ _) (lr_rel_delta_l ..)) }
  have graph a c : Entry_d M a c x ↔ M.mem a X ∧ M.mem c X ∧
      φ.toBinarySchema.denote ρ a c := by
    apply (rows a c).trans
    apply and_congr_right (fun _ => and_congr_right (fun _ => ?_))
    simp only [φ,BinarySchema.denote,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff]
    apply exists_congr
    intro q
    apply and_congr_right (fun _ => and_congr_right (fun _ => ?_))
    exact lr_rel_arguments_l nentry0_m nentry0_closed_l _ _ _ _ _ _ rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))))
  have owned : ∀ i, M.mem (ρ.bound i) P :=
    Fin.cases hX (Fin.cases hB (Fin.cases hT (Fin.cases hz
      (Fin.cases (trans X hX b hb) (Fin.cases (trans X hX τ hτ) (Fin.cases hH (fun i => Fin.elim0 i)))))))
  obtain ⟨f,hf,shape,entries⟩ := closed φ ρ X hX owned
  have eq := shape.eq_of_pairMember_iff hZF.1 rel (fun a b => (entries a b).trans (graph a b).symm)
  exact eq ▸ hf

end YesMetaZFC.SetTheory.Internal

/-! ## 同一完整背景函数名字证书的成员满运输

全部名字见证和条件仍使用原集合值。相对强迫部分是有界公式，图部分通过
实际关系的成员满像逐边比较，因而保留原解释的完整函数图。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models KP) (hN : N.Models KP)
  (e : M.Domain → N.Domain) (inj : Function.Injective e)
  (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
include inj full hM hN

theorem fn_bg_image_l {X B R z D A H x : M.Domain}
    (code : Fn_bg_d X B R z D A H x) (rel : M.IsSetRelation (kp_pair_l hM) x) :
    Fn_bg_d (e X) (e B) (e R) (e z) (e D) (e A) (e H) (e x) := by
  let ρ : Env M 8 := ⟨fun k => [X,B,R,z,D,A,H,x].get k,fun _ => x⟩
  let η : Env N 8 := ⟨fun k => [e X,e B,e R,e z,e D,e A,e H,e x].get k,fun _ => e x⟩
  have envEq : image_env_l e ρ = η := by
    have bound : (image_env_l e ρ).bound = η.bound := by
      funext k
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))) k
    exact congrArg (fun b => (⟨b,fun _ => e x⟩ : Env N 8)) bound
  change Formula.satisfies ρ fn_code0_m at code
  change Formula.satisfies η fn_code0_m
  simp only [fn_code0_m,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,entry_sat_l M hM.1] at code
  obtain ⟨b,hb,p,hp,t,ht,w,hw,τ,hτ,hbH,hpH,typed,rows⟩ := code
  have mem {a b : M.Domain} : N.mem (e a) (e b) ↔ M.mem a b := image_member_l e inj full
  have typed' := (delta0_image_l e inj full
    (lr_rel_delta_l fn_check0_m (.bound 5) (fun i => .bound (([6,7,8,4,9,10,3,2,1,0] : List (Fin 13)).get i)))
      (((((ρ.push b).push p).push t).push w).push τ)).mp typed
  simp only [image_env_push_l,envEq] at typed'
  have edge a c q := delta0_image_l e inj full
    (lr_rel_delta_l nentry0_m (.bound 8) (fun i => .bound (([9,10,11,7,3,2,1,0] : List (Fin 16)).get i)))
      ((((((((ρ.push b).push p).push t).push w).push τ).push a).push c).push q)
  simp only [image_env_push_l,envEq] at edge
  simp only [fn_code0_m,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,entry_sat_l N hN.1]
  refine ⟨e b,mem.mpr hb,e p,mem.mpr hp,e t,mem.mpr ht,e w,mem.mpr hw,e τ,mem.mpr hτ,
    mem.mpr hbH,mem.mpr hpH,typed',fun i y => ⟨?_,?_⟩⟩
  · intro iy
    obtain ⟨a,c,ac,rfl,rfl⟩ := (image_entries_l e full rel i y).mp iy
    obtain ⟨ha,hc,q,hq,qH,force⟩ := (rows a c).mp ac
    exact ⟨mem.mpr ha,mem.mpr hc,e q,mem.mpr hq,mem.mpr qH,(edge a c q).mp force⟩
  · rintro ⟨hi,hy,q,hq,qH,force⟩
    obtain ⟨a,ha,rfl⟩ := (full X i).mp hi
    obtain ⟨c,hc,rfl⟩ := (full X y).mp hy
    obtain ⟨q₀,hq₀,rfl⟩ := (full X q).mp hq
    exact (image_entry_iff_l e inj full (KP.exists_pair hM) hN.1 a c x).mp
      ((rows a c).mpr ⟨ha,hc,q₀,hq₀,mem.mp qH,(edge a c q₀).mpr force⟩)

end YesMetaZFC.Model.Forcing.Internal
