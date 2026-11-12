import YesMetaZFC.Model.Forcing.Collapse.ProductTopTruth
import YesMetaZFC.Model.Forcing.Collapse.ProductRealCollapse
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.SetTheory.InnerModel.Relative.TruthSyntax

/-! # 原规范实数并名字与有限前缀真值的初等运输

同一全乘积的两种字母表呈示决定同一规范名字。真值只使用冻结前缀
中的实际力迫见证；不要求目标泛型接受整个出发泛型的像。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {M : Structure.{u}} (hM : M.Models ZF)

theorem Rp_name_d.rebase_l {ω A A' P R r : M.Domain}
    (name : Rp_name_d hM ω A P r) (p : Fp_product_d hM ω A P R)
    (p' : Fp_product_d hM ω A' P R) : Rp_name_d hM ω A' P r := by
  have parts {n s} (hn : M.mem n ω) : Rp_part_d hM ω A n s ↔ Rp_part_d hM ω A' n s := by
    have move {A A'} (p : Fp_product_d hM ω A P R) (p' : Fp_product_d hM ω A' P R)
        (part : Rp_part_d hM ω A n s) : Rp_part_d hM ω A' n s := by
      obtain ⟨C,S,b,stage,real⟩ := part
      exact ⟨C,S,b,⟨stage.stage.rebase_l hM p p' hn,stage.relation,stage.member,stage.top⟩,real⟩
    exact ⟨move p p',move p' p⟩
  exact ⟨name.name,fun v => (name.members v).trans (exists_congr fun n => exists_congr fun s =>
    and_congr_right fun hn => and_congr (parts hn) Iff.rfl)⟩

variable {N : Structure.{v}} (hN : N.Models ZF) (e : M.Domain → N.Domain) (elem : Pe_d e)
include elem

theorem rp_name_image_l {ω A P r : M.Domain} (name : Rp_name_d hM ω A P r) :
    Rp_name_d hN (e ω) (e A) (e P) (e r) := by
  let ρ : Env M 4 := ⟨fun i => [ω,A,P,r].get i,fun _ => r⟩
  let φ := rp_name_m (.bound 0 : Term 4) (.bound 1) (.bound 2) (.bound 3)
  exact (rp_name_sat_l hN (image_env_l e ρ) _ _ _ _).mp
    ((elem φ (by simp -implicitDefEqProofs [φ]) ρ).mp ((rp_name_sat_l hM ρ _ _ _ _).mpr name))

theorem Rp_name_d.prefix_transfer_l {ω A P R r n C S W : M.Domain}
    (name : Rp_name_d hM ω A P r) (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hM)) A ω W)
    (product : Fp_product_d hM ω A P R) (stage : Fp_prefix_d hM ω A n C S) (hn : M.mem n ω)
    {G : M.Domain → Prop} {H : N.Domain → Prop}
    (g : Generic_d M P R P G) (h : Generic_d N (e P) (e R) (e P) H)
    (accepted : ∀ a, M.mem a C → G a → H (e a))
    {k} (φ : Formula 1 k) (hc : φ.FreeClosed) (ρ : Env M k)
    (params : ∀ i, ρ.bound i = r ∨ Name_d M C (ρ.bound i))
    (η : Env (extension_l M hM P R P G) k) (η' : Env (extension_l N hN (e P) (e R) (e P) H) k)
    (values : ∀ i, Qval_d M P R P G (ρ.bound i) (η.bound i))
    (images : ∀ i, Qval_d N (e P) (e R) (e P) H (e (ρ.bound i)) (η'.bound i))
    (truth : Formula.satisfies η φ) : Formula.satisfies η' φ := by
  obtain ⟨D,T,b,canonical⟩ := product.stage_l hM hw hn fa
  have eq : D = C := hM.1.eq_of_same_members D C
    (fun p => (canonical.stage.conditions p).trans (stage.conditions p).symm)
  subst D
  obtain ⟨a,ha,ga,forced⟩ := (name.prefix_truth_l hM hw fa product canonical hn g φ hc ρ params η values).mp truth
  exact (forcing_closed_truth_l hN (em_order_l hM.1 hN.1 e elem (product.order_l hM)) h
    φ hc (image_env_l e ρ) η' images).mp ⟨e a,accepted a ha ga,(em_forces_l e elem φ hc ρ P R P a).mp forced⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 冻结前缀的同一个实数名字保持指定背景图

检查名字以同一已接受前缀条件为基。先运输函数性质，再逐条运输原图边；
两侧完整函数具有同一源，故逐点一致给出背景对象相等。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u v w
variable {M : Structure.{u}} {N : Structure.{v}} {V : Structure.{w}}

theorem Rp_name_d.real_transfer_l (hM : M.Models ZF) (hN : N.Models ZF) (hV : V.Models KP)
    (e : M.Domain → N.Domain) (elem : Pe_d e)
    (k : M.Domain → V.Domain) (ki : Function.Injective k)
    (kf : ∀ a y, V.mem y (k a) ↔ ∃ b, M.mem b a ∧ k b = y) (l : N.Domain → V.Domain)
    {ω A P R r n C S W τ : M.Domain} (name : Rp_name_d hM ω A P r)
    (hw : M.IsOmega ω) (fa : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hM)) A ω W)
    (product : Fp_product_d hM ω A P R) (stage : Fp_prefix_d hM ω A n C S) (hn : M.mem n ω)
    {G : M.Domain → Prop} {H : N.Domain → Prop}
    (g : Generic_d M P R P G) (h : Generic_d N (e P) (e R) (e P) H)
    (accepted : ∀ p, M.mem p C → G p → H (e p))
    (fixedω : l (e ω) = k ω) (fixed : ∀ a, M.mem a ω → l (e a) = k a)
    (a : M.Domain → (extension_l M hM P R P G).Domain)
    (ground : ∀ s, Gval_d M P R P G s (a s))
    (f : (extension_l N hN (e P) (e R) (e P) H).Domain → V.Domain)
    (fi : Function.Injective f)
    (ff : ∀ a y, V.mem y (f a) ↔ ∃ b, (extension_l N hN (e P) (e R) (e P) H).mem b a ∧ f b = y)
    (base : ∀ s z, Gval_d N (e P) (e R) (e P) H s z → f z = l s)
    (nt : Name_d M C τ)
    {y : (extension_l M hM P R P G).Domain} {z : (extension_l N hN (e P) (e R) (e P) H).Domain}
    (vy : Qval_d M P R P G τ y) (vz : Qval_d N (e P) (e R) (e P) H (e τ) z)
    {x : V.Domain} (fy : Fn0_d (a ω) (a ω) y) (fx : Fn0_d (k ω) (k ω) x)
    (read : Fn_read_d k a y x) : f z = x := by
  let D := extension_l M hM P R P G
  let E := extension_l N hN (e P) (e R) (e P) H
  have O := product.order_l hM
  have O' := em_order_l hM.1 hN.1 e elem O
  have hD := preserves_zf_l O hM g
  have hE := preserves_zf_l O' hN h
  obtain ⟨p,hp,gp⟩ := (stage.extension_l hM product hw hn fa g).1.inhabited
  have sub : M.MemberSubset C P := fun p hp => ((stage.product_read_l hM product hn).1 p).mp hp |>.1
  have check (s : M.Domain) : ∃ t, ∃ u : E.Domain,
      Name_d M C t ∧ Qval_d M P R P G t (a s) ∧
      Qval_d N (e P) (e R) (e P) H (e t) u ∧ f u = l (e s) := by
    obtain ⟨t,ct,nt,_⟩ := zf_check_l M hM hp s
    have fullName := name_conditions_mono_l sub nt
    obtain ⟨v,vv⟩ := name_value_l (R := R) (z := P) (U := G) fullName
    have va : v = a s := Gval_d.unique_l O hM g ⟨p,t,gp,ct,vv⟩ (ground s)
    obtain ⟨u,vu⟩ := name_value_l (R := e R) (z := e P) (U := H) ((em_name_l hM.1 hN.1 e elem).mp fullName)
    exact ⟨t,u,nt,va ▸ vv,vu,base (e s) u ⟨e p,e t,accepted p hp gp,(em_check_l hM.1 hN.1 e elem).mp ct,vu⟩⟩
  obtain ⟨t,u,ntw,vt,vu,fu⟩ := check ω
  let ρ : Env M 3 := ⟨fun i => [t,t,τ].get i,fun _ => t⟩
  let η : Env D 3 := ⟨fun i => [a ω,a ω,y].get i,fun _ => y⟩
  let η' : Env E 3 := ⟨fun i => [u,u,z].get i,fun _ => z⟩
  let φ := fn0_m (.bound 0 : Term 3) (.bound 1) (.bound 2)
  have moved := name.prefix_transfer_l hM hN e elem hw fa product stage hn g h accepted φ
    (by simp -implicitDefEqProofs [φ]) ρ
    (Fin.cases (Or.inr ntw) (Fin.cases (Or.inr ntw) (Fin.cases (Or.inr nt) (fun i => Fin.elim0 i)))) η η'
    (Fin.cases vt (Fin.cases vt (Fin.cases vy (fun i => Fin.elim0 i))))
    (Fin.cases vu (Fin.cases vu (Fin.cases vz (fun i => Fin.elim0 i)))) ((fn0_sat_l hD.1 η _ _ _).mpr fy)
  have fz : Fn0_d (k ω) (k ω) (f z) := by
    have out := (fn0_sat_l hV.1 (image_env_l f η') (.bound 0) (.bound 1) (.bound 2)).mp
      ((delta0_image_l f fi ff (fn0_delta_l _ _ _) η').mp moved)
    change Fn0_d (f u) (f u) (f z) at out
    simpa only [fu,fixedω] using out
  have edge {i j : V.Domain} (ij : Entry_d V i j x) : Entry_d V i j (f z) := by
    obtain ⟨s,t,es,et,old⟩ := (read i j).mp ij
    have hs : M.mem s ω := (image_member_l k ki kf).mp (es.symm ▸ (fx.bound_l ij).1)
    have ht : M.mem t ω := (image_member_l k ki kf).mp (et.symm ▸ (fx.bound_l ij).2)
    obtain ⟨σ,b,ns,vs,vs',fb⟩ := check s
    obtain ⟨τ',c,ns',vt,vt',fc⟩ := check t
    let ρ : Env M 3 := ⟨fun i => [σ,τ',τ].get i,fun _ => τ⟩
    let η : Env D 3 := ⟨fun i => [a s,a t,y].get i,fun _ => y⟩
    let η' : Env E 3 := ⟨fun i => [b,c,z].get i,fun _ => z⟩
    let φ := entry_m (.bound 0 : Term 3) (.bound 1) (.bound 2)
    have tr := name.prefix_transfer_l hM hN e elem hw fa product stage hn g h accepted φ
      (by simp -implicitDefEqProofs [φ]) ρ
      (Fin.cases (Or.inr ns) (Fin.cases (Or.inr ns') (Fin.cases (Or.inr nt) (fun i => Fin.elim0 i)))) η η'
      (Fin.cases vs (Fin.cases vt (Fin.cases vy (fun i => Fin.elim0 i))))
      (Fin.cases vs' (Fin.cases vt' (Fin.cases vz (fun i => Fin.elim0 i)))) ((entry_sat_l D hD.1 η _ _ _).mpr old)
    have out := (image_entry_iff_l f fi ff (KP.exists_pair (ZF.modelsKP hE)) hV.1 b c z).mp
      ((entry_sat_l E hE.1 η' _ _ _).mp tr)
    simpa only [fb,fc,fixed s hs,fixed t ht,es,et] using out
  have X := fn0_function_l hV fx
  have Z := fn0_function_l hV fz
  apply (X.1.1.eq_of_pairMember_iff hV.1 Z.1.1 (fun i j => ⟨edge,?_⟩)).symm
  intro ij
  obtain ⟨k,_,ik⟩ := X.2.2 i (Z.input_mem_of_pairMember ij)
  exact Z.1.2 i k j (edge ik) ij ▸ ik

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原 8.6：固定前缀后的派生模型真值沿原嵌入运输

出发断言在实际全乘积泛型中成立，实数参数由已冻结前缀的名字解释。
目标仅接受该前缀滤子的像。规范实数并名字、完整原公式与同一参数图
同时运输，结论使用目标同一个泛型扩张中的实际派生模型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u v w
variable {M : Structure.{u}} {N : Structure.{v}} {V : Structure.{w}}

def Fp_truth_d (hM : M.Models ZF) (k : M.Domain → V.Domain) (ω A P R C : M.Domain)
    (H₀ : M.Domain → Prop) {n} (φ : Formula 1 n) (x : Fin n → V.Domain) : Prop :=
  (∀ i, Fn0_d (k ω) (k ω) (x i)) ∧
  ∃ G : M.Domain → Prop, Generic_d M P R P G ∧ (∀ p, M.mem p C → (G p ↔ H₀ p)) ∧
  ∃ r, Rp_name_d hM ω A P r ∧ ∃ Z : (extension_l M hM P R P G).Domain,
    Qval_d M P R P G r Z ∧
    ∃ a : M.Domain → (extension_l M hM P R P G).Domain,
      (∀ s, Gval_d M P R P G s (a s)) ∧
    ∃ τ : Fin n → M.Domain, ∃ y : Fin n → (extension_l M hM P R P G).Domain,
      (∀ i, Name_d M C (τ i) ∧ Qval_d M P R P G (τ i) (y i) ∧ Fn_read_d k a (y i) (x i)) ∧
      Relative.Dr_truth_d Z φ y

theorem Fp_truth_d.transfer_l (hM : M.Models ZF) (hN : N.Models ZF) (hV : V.Models KP)
    (e : M.Domain → N.Domain) (elem : Pe_d e)
    (k : M.Domain → V.Domain) (ki : Function.Injective k)
    (kf : ∀ a y, V.mem y (k a) ↔ ∃ b, M.mem b a ∧ k b = y) (l : N.Domain → V.Domain)
    {ω A P R n C S W : M.Domain} (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hM)) A ω W)
    (product : Fp_product_d hM ω A P R) (stage : Fp_prefix_d hM ω A n C S) (hn : M.mem n ω)
    {H₀ : M.Domain → Prop} {H : N.Domain → Prop} (h : Generic_d N (e P) (e R) (e P) H)
    (accepted : ∀ p, H₀ p → H (e p))
    (fixedω : l (e ω) = k ω) (fixed : ∀ a, M.mem a ω → l (e a) = k a)
    {A' r' : N.Domain} (product' : Fp_product_d hN (e ω) A' (e P) (e R))
    (name' : Rp_name_d hN (e ω) A' (e P) r')
    {Z' : (extension_l N hN (e P) (e R) (e P) H).Domain}
    (value' : Qval_d N (e P) (e R) (e P) H r' Z')
    (f : (extension_l N hN (e P) (e R) (e P) H).Domain → V.Domain)
    (fi : Function.Injective f)
    (ff : ∀ a y, V.mem y (f a) ↔ ∃ b, (extension_l N hN (e P) (e R) (e P) H).mem b a ∧ f b = y)
    (base : ∀ s z, Gval_d N (e P) (e R) (e P) H s z → f z = l s)
    {d} {φ : Formula 1 d} (hc : φ.FreeClosed) {x : Fin d → V.Domain}
    (truth : Fp_truth_d hM k ω A P R C H₀ φ x) :
    ∃ y : Fin d → (extension_l N hN (e P) (e R) (e P) H).Domain,
      (∀ i, f (y i) = x i) ∧ Relative.Dr_truth_d Z' φ y := by
  obtain ⟨real,G,g,frozen,r,name,Z,value,a,ground,τ,y,params,old⟩ := truth
  let D := extension_l M hM P R P G
  let E := extension_l N hN (e P) (e R) (e P) H
  have hD := preserves_zf_l (product.order_l hM) hM g
  have hE := preserves_zf_l (product'.order_l hN) hN h
  have accept p hp gp := accepted p ((frozen p hp).mp gp)
  have sub : M.MemberSubset C P := fun p hp => ((stage.product_read_l hM product hn).1 p).mp hp |>.1
  have movedName := (rp_name_image_l hM hN e elem name).rebase_l hN
    (fp_product_image_l hM hN e elem product) product'
  have eq : e r = r' := movedName.unique_l hN name'
  have rz : Qval_d N (e P) (e R) (e P) H (e r) Z' := eq.symm ▸ value'
  have targetName i : Name_d N (e P) (e (τ i)) :=
    (em_name_l hM.1 hN.1 e elem).mp (name_conditions_mono_l sub (params i).1)
  -- 名字像直接给出商元素，无须选择目标解释或商代表元。
  let z : Fin d → E.Domain := fun i => Quot.mk (Name_eq_d N (e P) (e R) (e P) H) ⟨e (τ i),targetName i⟩
  have vz i : Qval_d N (e P) (e R) (e P) H (e (τ i)) (z i) := ⟨targetName i,rfl⟩
  obtain ⟨Z₀,v₀,members⟩ := name.value_l hM hw fa product g
  have realValue i : Fn0_d (a ω) (a ω) (y i) :=
    ((members (y i)).mp ((qval_unique_l v₀ value).symm ▸ old.1 i)).function_l hM hw fa product g a ground
  refine ⟨z,fun i => name.real_transfer_l hM hN hV e elem k ki kf l hw fa product stage hn g h accept
    fixedω fixed a ground f fi ff base (params i).1 (params i).2.1 (vz i) (realValue i) (real i) (params i).2.2,?_⟩
  let ρ : Env M (d+1) := ⟨Fin.cases r τ,fun _ => r⟩
  let η : Env D (d+1) := ⟨Fin.cases Z y,fun _ => Z⟩
  let η' : Env E (d+1) := ⟨Fin.cases Z' z,fun _ => Z'⟩
  let ψ := Relative.dr_m φ (.newest : Term (d+1)) (fun i => .bound i.succ)
  have tr := name.prefix_transfer_l hM hN e elem hw fa product stage hn g h accept ψ
    (Relative.dr_closed_l φ hc _ _ rfl (fun _ => rfl)) ρ
    (Fin.cases (Or.inl rfl) (fun i => Or.inr (params i).1)) η η'
    (Fin.cases value (fun i => (params i).2.1)) (Fin.cases rz vz)
    ((Relative.dr_sat_l (ZF.modelsKP hD) φ hc η _ _).mpr old)
  exact (Relative.dr_sat_l (ZF.modelsKP hE) φ hc η' _ _).mp tr

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原派生模型断言的实际共同有限前缀

规范实数并的每个参数有真实有限前缀名字。只对公式的参数个数作宿主
有限归纳，取一个共同内部自然数界，再补长这些名字而保持全乘积解释。
所得正长度前缀直接满足原 Fp_truth_d，供 8.5 的保存端点使用。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

private theorem rp_finite_bound_l {ω : M.Domain} (hw : M.IsOmega ω) {n}
    (a : Fin n → M.Domain) (ha : ∀ k, M.mem (a k) ω) :
    ∃ m, M.mem m ω ∧ ∀ k, M.MemberSubset (a k) m := by
  induction n with
  | zero =>
    obtain ⟨o,_,ho⟩ := hw.1.1
    exact ⟨o,ho,fun k => Fin.elim0 k⟩
  | succ n ih =>
    obtain ⟨m,hm,bound⟩ := ih (fun k => a k.succ) (fun k => ha k.succ)
    rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare (a 0) (ha 0) m hm with eq | am | ma
    · exact ⟨m,hm,Fin.cases (fun z hz => (eq z).mp hz) bound⟩
    · exact ⟨m,hm,Fin.cases ((hw.members_areOrdinals (ZF.modelsKP hZF) m hm).transitive (a 0) am) bound⟩
    · exact ⟨a 0,ha 0,Fin.cases (fun _ h => h) (fun k z hz =>
        (hw.members_areOrdinals (ZF.modelsKP hZF) (a 0) (ha 0)).transitive m ma z (bound k z hz))⟩

theorem Rp_name_d.truth_prefix_l {V : Structure.{v}} (k : M.Domain → V.Domain)
    {ω A P R W r : M.Domain} (name : Rp_name_d hZF ω A P r)
    (hw : M.IsOmega ω) (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    {Z : (extension_l M hZF P R P G).Domain} (value : Qval_d M P R P G r Z)
    (j : M.Domain → (extension_l M hZF P R P G).Domain)
    (ground : ∀ a, Gval_d M P R P G a (j a))
    {n} {φ : Formula 1 n} {y : Fin n → (extension_l M hZF P R P G).Domain} {x : Fin n → V.Domain}
    (real : ∀ a, Fn0_d (k ω) (k ω) (x a)) (read : ∀ a, Fn_read_d k j (y a) (x a))
    (truth : Relative.Dr_truth_d Z φ y) :
    ∃ i m C S, M.mem i ω ∧ M.SuccessorOf m i ∧ M.mem m ω ∧
      Fp_prefix_d hZF ω A m C S ∧ Fp_truth_d hZF k ω A P R C G φ x := by
  obtain ⟨Z₀,value₀,members⟩ := name.value_l hZF hw fa product generic
  have eq := qval_unique_l value₀ value
  have each a : ∃ m C S τ, M.mem m ω ∧ Fp_prefix_d hZF ω A m C S ∧
      Name_d M C τ ∧ Qval_d M P R P G τ (y a) := by
    obtain ⟨m,C,S,_,hm,stage,_,_,τ,_,val,target,_⟩ :=
      (members (y a)).mp (eq.symm ▸ truth.1 a)
    exact ⟨m,C,S,τ,hm,stage.stage,qval_name_l val,target⟩
  obtain ⟨a,stages⟩ := Classical.axiomOfChoice each
  have natural s : M.mem (a s) ω := by
    obtain ⟨_,_,_,ha,_⟩ := stages s
    exact ha
  obtain ⟨i,hi,bound⟩ := rp_finite_bound_l hZF hw a natural
  obtain ⟨m,succ,hm⟩ := hw.1.2 i hi
  obtain ⟨C,S,later⟩ := product.prefix_l hZF hm
  have names s : ∃ τ, Name_d M C τ ∧ Qval_d M P R P G τ (y s) := by
    obtain ⟨D,T,τ,ha,stage,nt,val⟩ := stages s
    have sub : M.MemberSubset (a s) m := fun z hz => (succ z).mpr (Or.inl (bound s z hz))
    exact stage.name_extend_l hZF hw ha hm fa product later sub generic nt val
  obtain ⟨τ,values⟩ := Classical.axiomOfChoice names
  exact ⟨i,m,C,S,hi,succ,hm,later,real,G,generic,(fun _ _ => Iff.rfl),r,name,Z,value,j,ground,
    τ,y,fun a => ⟨(values a).1,(values a).2,read a⟩,truth⟩

end YesMetaZFC.Model.Forcing.Internal
