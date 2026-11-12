import YesMetaZFC.Model.Forcing.Functions.CheckCompare
import YesMetaZFC.Model.Forcing.Functions.ValueIsomorphism
import YesMetaZFC.Model.Forcing.Ground.CheckPool

/-! # 检查子集名字在两侧泛型扩张中的实际实数值

逐成员比较给出双向函数性及完整图读取。回拉保留已有原名字，正向则
实际构造目标值；任意原实数先由检查子集名字规范化，再使用同一比较。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem Ck_bound_d.real_pull_l (hM : M.Models ZF) (hN : N.Models ZF)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {B R z b D ω τ : M.Domain} (bound : Ck_bound_d B b D τ)
    (product : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hM)) D ω ω)
    (O : Cond_order_d M B R z) {G : M.Domain → Prop} {H : N.Domain → Prop}
    (g : Generic_d M B R z G) (h : Generic_d N (e B) (e R) (e z) H)
    (same : ∀ p, G p ↔ H (e p)) (hb : G b)
    (k : N.Domain → (extension_l N hN (e B) (e R) (e z) H).Domain)
    (ground : ∀ a, Gval_d N (e B) (e R) (e z) H a (k a))
    {y : (extension_l N hN (e B) (e R) (e z) H).Domain}
    (value : Qval_d N (e B) (e R) (e z) H (e τ) y)
    (real : Fn0_d (k (e ω)) (k (e ω)) y) :
    Fn_value_d hM (k ∘ e) B R z ω τ G y := by
  have O' := image_cond_order_l (ZF.modelsKP hM) hN.1 e inj full O
  obtain ⟨k₀,kc,kf,ki⟩ := check_map_l O' hN h ((same b).mp hb)
  have eq : k₀ = k := funext fun a => (gval_check_map_l O' hN h ((same b).mp hb) k₀ kc a (k a)).mp (ground a)
  subst k₀
  obtain ⟨j,jc,jf,ji⟩ := check_map_l O hM g hb
  obtain ⟨x,vx⟩ := name_value_l (R := R) (z := z) (U := G) (bound.name_l hM (g.proper b hb).1)
  obtain ⟨equivalent,read⟩ := bound.real_compare_l hM hN e inj full product O g h same j k jc kc ji jf ki kf vx value
  exact ⟨j,x,vx,fun a => (gval_check_map_l O hM g hb j jc a (j a)).mpr rfl,equivalent.mpr real,read real⟩

/-- 反向实际构造目标值，而不是预设原实数已经在目标扩张中。 -/
theorem Ck_bound_d.real_push_l (hM : M.Models ZF) (hN : N.Models ZF)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {B R z b D ω τ : M.Domain} (bound : Ck_bound_d B b D τ)
    (product : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hM)) D ω ω)
    (O : Cond_order_d M B R z) {G : M.Domain → Prop} {H : N.Domain → Prop}
    (g : Generic_d M B R z G) (h : Generic_d N (e B) (e R) (e z) H)
    (same : ∀ p, G p ↔ H (e p)) (hb : G b)
    (j : M.Domain → (extension_l M hM B R z G).Domain)
    (base : ∀ a, Gval_d M B R z G a (j a))
    (k : N.Domain → (extension_l N hN (e B) (e R) (e z) H).Domain)
    (ground : ∀ a, Gval_d N (e B) (e R) (e z) H a (k a))
    {x : (extension_l M hM B R z G).Domain} (value : Qval_d M B R z G τ x)
    (real : Fn0_d (j ω) (j ω) x) :
    ∃ y, Qval_d N (e B) (e R) (e z) H (e τ) y ∧
      Fn0_d (k (e ω)) (k (e ω)) y ∧ Fn_read_d (k ∘ e) j x y := by
  have O' := image_cond_order_l (ZF.modelsKP hM) hN.1 e inj full O
  obtain ⟨j₀,jc,jf,ji⟩ := check_map_l O hM g hb
  have eqj : j₀ = j := funext fun a => (gval_check_map_l O hM g hb j₀ jc a (j a)).mp (base a)
  subst j₀
  obtain ⟨k₀,kc,kf,ki⟩ := check_map_l O' hN h ((same b).mp hb)
  have eqk : k₀ = k := funext fun a => (gval_check_map_l O' hN h ((same b).mp hb) k₀ kc a (k a)).mp (ground a)
  subst k₀
  have target := (image_ck_bound_l hM hN e inj full).mp bound
  obtain ⟨y,vy⟩ := name_value_l (R := e R) (z := e z) (U := H)
    (target.name_l hN (h.proper (e b) ((same b).mp hb)).1)
  obtain ⟨equivalent,read⟩ := bound.real_compare_l hM hN e inj full product O g h same j k jc kc ji jf ki kf value vy
  have fy := equivalent.mp real
  exact ⟨y,vy,fy,read fy⟩

/-- 任意原实数先规范化，再实际提升到目标泛型扩张；保留原值的完整图。 -/
theorem check_real_image_l (hM : M.Models ZF) (hN : N.Models ZF)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {B R z ω : M.Domain} (O : Cond_order_d M B R z) {G : M.Domain → Prop} {H : N.Domain → Prop}
    (g : Generic_d M B R z G) (h : Generic_d N (e B) (e R) (e z) H) (same : ∀ p, G p ↔ H (e p))
    (j : M.Domain → (extension_l M hM B R z G).Domain) (base : ∀ a, Gval_d M B R z G a (j a))
    (k : N.Domain → (extension_l N hN (e B) (e R) (e z) H).Domain)
    (ground : ∀ a, Gval_d N (e B) (e R) (e z) H a (k a))
    {x : (extension_l M hM B R z G).Domain} (real : Fn0_d (j ω) (j ω) x) :
    ∃ τ y, Qval_d M B R z G τ x ∧ Qval_d N (e B) (e R) (e z) H (e τ) y ∧
      Fn0_d (k (e ω)) (k (e ω)) y ∧ Fn_read_d (k ∘ e) j x y := by
  have hE := preserves_zf_l O hM g
  obtain ⟨b,hb⟩ := g.inhabited
  obtain ⟨j₀,jc,jf,ji⟩ := check_map_l O hM g hb
  have eq : j₀ = j := funext fun a => (gval_check_map_l O hM g hb j₀ jc a (j a)).mp (base a)
  subst j₀
  obtain ⟨D,product⟩ := ZF.exists_cartesianProduct hM (kp_pair_l (ZF.modelsKP hM)) ω ω
  obtain ⟨W,pool⟩ := ck_pool_exists_l hM (g.proper b hb).1 D
  obtain ⟨t,check,_,_⟩ := zf_check_l M hM (g.proper b hb).1 D
  have product' := image_product_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hE)) j ji jf product
  have sub : ∀ v, v ∈ x → v ∈ j D := by
    intro v hv
    obtain ⟨a,ha,c,hc,pair⟩ := real.1 v hv
    exact (product' v).mpr ⟨a,ha,c,hc,pair⟩
  obtain ⟨τ,hτ,value⟩ := pool.represent_l hM O (g.proper b hb).1 check g (jc D t check) sub
  obtain ⟨y,vy,fy,read⟩ := ((pool τ).mp hτ).real_push_l hM hN e inj full product O g h same hb j base k ground value real
  exact ⟨τ,y,value,vy,fy,read⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原秩模型的实际名字覆盖背景泛型扩张的所有实数

在原模型构造 ω² 的检查子集名字库。秩层子集闭包使它覆盖背景中
全部规范名字；求值回读则保持同一个背景实数。原泛型由大泛型直接
限制得到，不再要求额外的名字覆盖证书或完整初等包含。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {c X R θ : M.Domain}
  (source : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (trans : M.TransitiveSet X)
  (rank : V_d (kp_pair_l (ZF.modelsKP hZF)) θ X)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).Models ZF)
include trans rank

theorem Smem_d.check_real_names_l
    {B T z ω : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).Domain}
    (O : Cond_order_d (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1) B T z)
    {H : M.Domain → Prop} (generic : Generic_d M B.val T.val z.val H)
    (k : M.Domain → (extension_l M hZF B.val T.val z.val H).Domain)
    (ground : ∀ a, Gval_d M B.val T.val z.val H a (k a)) :
    let N := smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1
    let G : N.Domain → Prop := H ∘ Subtype.val
    Generic_d N B T z G ∧ ∀ x, Fn0_d (k ω.val) (k ω.val) x →
      ∃ τ, Fn_value_d native (k ∘ Subtype.val) B T z ω τ G x := by
  let N := smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1
  let E := extension_l M hZF B.val T.val z.val H
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l (kp_pair_l (ZF.modelsKP hZF)) source trans
  have g := generic.ground_pull_l (ZF.modelsKP native) hZF.1 Subtype.val inj full
  have O' := image_cond_order_l (ZF.modelsKP native) hZF.1 Subtype.val inj full O
  have hE := preserves_zf_l O' hZF generic
  obtain ⟨b,hb⟩ := g.inhabited
  obtain ⟨j,jc,jf,ji⟩ := check_map_l O' hZF generic hb
  have eq : j = k := funext fun a => (gval_check_map_l O' hZF generic hb j jc a (k a)).mp (ground a)
  subst j
  obtain ⟨D,product⟩ := ZF.exists_cartesianProduct native (kp_pair_l (ZF.modelsKP native)) ω ω
  obtain ⟨W,pool⟩ := ck_pool_exists_l native (g.proper b hb).1 D
  have pool' := Smem_d.check_pool_l hZF source trans rank native pool
  obtain ⟨t,check,_,_⟩ := zf_check_l N native (g.proper b hb).1 D
  have check' := image_check_l Subtype.val inj full (ZF.modelsKP native) hZF.1 check
  have product' := image_product_l (hEN := hZF.1) (hPN := KP.exists_pair (ZF.modelsKP hZF)) Subtype.val inj full product
  have productE := image_product_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hE)) k ji jf product'
  refine ⟨g,fun x real => ?_⟩
  have sub : E.MemberSubset x (k D.val) := by
    intro v hv
    obtain ⟨a,ha,d,hd,pair⟩ := real.1 v hv
    exact (productE v).mpr ⟨a,ha,d,hd,pair⟩
  obtain ⟨τ,hτ,value⟩ := pool'.represent_l hZF O' (generic.proper b.val hb).1 check' generic (jc D.val t.val check') sub
  obtain ⟨τ₀,hτ₀,rfl⟩ := (full W τ).mp hτ
  exact ⟨τ₀,((pool τ₀).mp hτ₀).real_pull_l native hZF Subtype.val inj full product O g generic
    (fun _ => Iff.rfl) hb k ground value real⟩

/-- 原背景图保持不变；只把规范化后的名字收回原秩模型。 -/
theorem Smem_d.check_real_value_l {V : Structure}
    {B T z ω : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).Domain}
    (O : Cond_order_d (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1) B T z)
    {H : M.Domain → Prop} (generic : Generic_d M B.val T.val z.val H)
    {k : M.Domain → V.Domain} {τ : M.Domain} {x : V.Domain}
    (named : Fn_value_d hZF k B.val T.val z.val ω.val τ H x) :
    ∃ σ, Fn_value_d native (k ∘ Subtype.val) B T z ω σ (H ∘ Subtype.val) x := by
  let N := smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l (kp_pair_l (ZF.modelsKP hZF)) source trans
  have O' := image_cond_order_l (ZF.modelsKP native) hZF.1 Subtype.val inj full O
  obtain ⟨j,y,_,ground,real,read⟩ := named
  obtain ⟨b,hb⟩ := generic.inhabited
  obtain ⟨j₀,jc,_,ji⟩ := check_map_l O' hZF generic hb
  have eq : j₀ = j := funext fun a => (gval_check_map_l O' hZF generic hb j₀ jc a (j a)).mp (ground a)
  subst j₀
  obtain ⟨σ,l,v,value,base,fv,old⟩ :=
    (Smem_d.check_real_names_l hZF source trans rank native O generic j ground).2 y real
  refine ⟨σ,l,v,value,base,fv,fun a d => ⟨?_,?_⟩⟩
  · intro ad
    obtain ⟨a₀,d₀,ea,ed,edge⟩ := (read a d).mp ad
    obtain ⟨a₁,d₁,ea',ed',edge'⟩ := (old (j a₀) (j d₀)).mp edge
    exact ⟨a₁,d₁,(congrArg k (ji ea')).trans ea,(congrArg k (ji ed')).trans ed,edge'⟩
  · rintro ⟨a₀,d₀,rfl,rfl,edge⟩
    exact (read (k a₀.val) (k d₀.val)).mpr
      ⟨a₀.val,d₀.val,rfl,rfl,(old (j a₀.val) (j d₀.val)).mpr ⟨a₀,d₀,rfl,rfl,edge⟩⟩

end YesMetaZFC.Model.Forcing.Internal
