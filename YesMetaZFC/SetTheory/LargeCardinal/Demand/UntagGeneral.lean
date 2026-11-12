import YesMetaZFC.Model.SetTheory.Demand.Untag
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.Model.SetTheory.Demand.TagSyntax
import YesMetaZFC.Model.SetTheory.Embedding.Theory
import YesMetaZFC.SetTheory.LargeCardinal.Demand.AlphabetGround
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ProjectionSpace
import YesMetaZFC.SetTheory.LargeCardinal.Demand.GeneralProjection
import YesMetaZFC.Model.SetTheory.Internal.RealTrace

/-! # 标签重编码进入实际泛型扩张

标签行、解码图和逆像树都由成员满嵌入搬运。新有限列由已有内部归纳
回收，因而搬运后的数据仍描述扩张自己的全部有限节点。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include inj full

theorem Td_retag_d.image_l {ω A S U V e o T U' V' : M.Domain}
    (r : Td_retag_d hM ω A S U V e o T U' V') (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω)) :
    Nonempty (Td_retag_d hN (j ω) (j A) (j S) (j U) (j V) (j e) (j o) (j T) (j U') (j V')) := by
  have member {a b : M.Domain} : N.mem (j a) (j b) ↔ M.mem a b := image_member_l j inj full
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  have tag {a b c d} (h : Td_tag_d a b c d) : Td_tag_d (j a) (j b) (j c) (j d) := by
    obtain ⟨x,y,z,t,u,v,w,ct,tv,uy,vz,dw,wy⟩ := h
    exact ⟨j x,j y,j z,j t,j u,j v,j w,image_kpair_l j full ct,image_kpair_l j full tv,
      image_kpair_l j full uy,image_kpair_l j full vz,image_kpair_l j full dw,image_kpair_l j full wy⟩
  have row {b U C : M.Domain} (line : ∀ z, M.mem z C ↔ ∃ a, M.mem a U ∧ KPair_d M z b a) :
      ∀ z, N.mem z (j C) ↔ ∃ a, N.mem a (j U) ∧ KPair_d N z (j b) a := by
    intro z
    constructor
    · intro hz
      obtain ⟨c,hc,eq⟩ := (full C z).mp hz
      obtain ⟨a,ha,ca⟩ := (line c).mp hc
      exact ⟨j a,member.mpr ha,eq ▸ image_kpair_l j full ca⟩
    · rintro ⟨a,ha,pair⟩
      obtain ⟨a₀,ha₀,eq⟩ := (full U a).mp ha
      subst a
      obtain ⟨c,ca⟩ := (I).total b a₀
      exact (full C z).mpr ⟨c,(line c).mpr ⟨a₀,ha₀,ca⟩,(J).unique (image_kpair_l j full ca) pair⟩
  have bij : N.IsSetBijectionFromTo J (j r.f) (j r.Y') (j r.Y) := by
    refine ⟨image_injection_l j inj full r.map.1,?_⟩
    intro y hy
    obtain ⟨y₀,hy₀,eq⟩ := (full r.Y y).mp hy
    obtain ⟨x,hx,xy⟩ := r.map.2 y₀ hy₀
    exact ⟨j x,member.mpr hx,eq ▸ (entry x y₀ r.f).mp xy⟩
  refine ⟨⟨j r.P,j r.Y,j r.F,j r.P',j r.Y',j r.F',j r.f,
    image_product_l j inj full r.pair,image_product_l j inj full r.triple,
    image_product_l j inj full r.pair',image_product_l j inj full r.triple',
    image_fseq_l hM hN j inj full hw hw' r.space,image_fseq_l hM hN j inj full hw hw' r.space',
    image_tree_l j inj full r.source,bij,?_,
    image_tree_pullback_l hM hN j inj full r.map.1.1 r.space' r.pull,row r.left,row r.right⟩⟩
  intro x y
  constructor
  · intro xy
    obtain ⟨a,b,ab,rfl,rfl⟩ := (image_entries_l j full r.map.1.1.1.1 x y).mp xy
    have data := (r.decode a b).mp ab
    exact ⟨member.mpr data.1,tag data.2⟩
  · rintro ⟨hx,xy⟩
    obtain ⟨a,ha,eq⟩ := (full r.Y' x).mp hx
    subst x
    obtain ⟨b,_,ab⟩ := r.map.1.1.2.2 a ha
    have eq := (td_tag_unique_l hN.1 (tag ((r.decode a b).mp ab).2) xy).mp rfl
    exact eq ▸ (entry a b r.f).mp ab

end YesMetaZFC.SetTheory.Internal

/-! ## 实际初等根腿运输标签树与最小字母域

先在原生关系模型之间应用完整公式，再由传递目标的成员满包含读出。
初等根腿本身不被当作成员满嵌入。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_retag_d.native_map_l {Ω c d X R Y S j : M.Domain}
    (hw : M.IsOmega Ω) (source : Smdl_d I c X R) (target : Smdl_d I d Y S)
    (map : Smap_d I Ω c d X Y j)
    (hX : (smdl_structure_l I (R := R) source.2.1).Models ZF)
    (hY : (smdl_structure_l I (R := S) target.2.1).Models ZF)
    {v : Fin 10 → (smdl_structure_l I (R := R) source.2.1).Domain}
    {w : Fin 10 → (smdl_structure_l I (R := S) target.2.1).Domain}
    (frame : Td_retag_d hX (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9))
    (points : ∀ i, Rd_entry_d (v i).val (w i).val j) :
    Nonempty (Td_retag_d hY (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9)) := by
  let φ : Formula 1 10 := td_retag_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
    (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9)
  let ρ := (⟨v,fun _ => v 0⟩ : Env _ 10)
  let η := (⟨w,fun _ => w 0⟩ : Env _ 10)
  exact (td_retag_sat_l hY η ..).mp
    ((smap_source_l I hZF hw source target map φ
      (td_retag_m_freeClosed _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) ρ η points).mp
      ((td_retag_sat_l hX ρ ..).mpr ⟨frame⟩))

theorem Td_alphabet_d.native_map_l {Ω c d X R Y S j : M.Domain}
    (hw : M.IsOmega Ω) (source : Smdl_d I c X R) (target : Smdl_d I d Y S)
    (map : Smap_d I Ω c d X Y j)
    (hX : Extensional (smdl_structure_l I (R := R) source.2.1))
    (hY : Extensional (smdl_structure_l I (R := S) target.2.1))
    {v : Fin 3 → (smdl_structure_l I (R := R) source.2.1).Domain}
    {w : Fin 3 → (smdl_structure_l I (R := S) target.2.1).Domain}
    (alphabet : Td_alphabet_d (v 0) (v 1) (v 2))
    (points : ∀ i, Rd_entry_d (v i).val (w i).val j) : Td_alphabet_d (w 0) (w 1) (w 2) := by
  let φ : Formula 1 3 := td_alphabet_m (.bound 0) (.bound 1) (.bound 2)
  let ρ := (⟨v,fun _ => v 0⟩ : Env _ 3)
  let η := (⟨w,fun _ => w 0⟩ : Env _ 3)
  exact (td_alphabet_sat_l hY η ..).mp
    ((smap_source_l I hZF hw source target map φ
      (td_alphabet_m_freeClosed _ _ _ rfl rfl rfl) ρ η points).mp
      ((td_alphabet_sat_l hX ρ ..).mpr alphabet))

end YesMetaZFC.SetTheory.Internal

/-! ## demanding 投影去标签，保留同一原实数

解码两张辅助图，原实数图不动。三坐标合成图经真实逆像关系回到原树，
第一辅助图仍满射，故解码保留完整 demanding 投影。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 合成图在实际三字母积内时，原实数的每个取值都在其第一因子内。 -/
theorem Td_projection_d.input_l {ω X A U V P Y F S x : M.Domain}
    (projection : Td_projection_d hZF ω U V Y F S x)
    (triple : M.IsCartesianProduct I Y A P) (fx : Fn0_d ω X x) : Fn0_d ω A x := by
  obtain ⟨q,a,b,_,_,_,fq,_,join⟩ := projection
  apply fx.retarget_l
  intro i y iy
  obtain ⟨y',u,v,t,z,iy',_,_,_,zy,iz⟩ := join.2 i (fx.bound_l iy).1
  obtain ⟨r,hr,s,_,zr⟩ := (triple z).mp (fq.bound_l iz).2
  have eq := ((I).injective zy zr).1
  exact (fn0_function_l (ZF.modelsKP hZF) fx).1.2 i r y (eq ▸ iy') iy ▸ hr

end YesMetaZFC.SetTheory.LargeCardinal

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive LargeCardinal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_retag_d.projection_l {ω A S U V e o T U' V' X x : M.Domain}
    (r : Td_retag_d hZF ω A S U V e o T U' V') (hw : M.IsOmega ω)
    (fx : Fn0_d ω X x) (projection : Td_projection_d hZF ω U' V' r.Y' r.F' T x) :
    Td_projection_d hZF ω U V r.Y r.F S x := by
  have input := projection.input_l hZF r.triple' fx
  obtain ⟨q,c,d,fc,onto,fd,fq,branch,joined⟩ := projection
  obtain ⟨a,fa,left,cover⟩ := tag_graph_decode_l hZF r.left fc
  obtain ⟨b,fb,right,_⟩ := tag_graph_decode_l hZF r.right fd
  obtain ⟨_,_,t,_,_,_,join⟩ := tg_join_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) input)
    (fn0_function_l (ZF.modelsKP hZF) fa) (fn0_function_l (ZF.modelsKP hZF) fb)
  have recode := td_tag_join_l hZF r.map.1.1 r.decode input fa fb fq left right join joined
  exact ⟨t,a,b,fa,cover onto,fb,join.typed_l hZF input fa fb r.pair r.triple,
    (r.branch_l hZF hw (fn0_function_l (ZF.modelsKP hZF) fq) recode).mp branch,join⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 同一迭代树上逐枝去标签

每条实际共尾良基枝的锥给出原根的完整初等腿。运输同一标签框架后，
在该枝自己的传递模型中去标签；原对局、迭代树和临界点下界全部保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_fixed_gp_d.untag_l {Ω c X R z f : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω A S U V e o T U' V' : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω) (eqω : ω.val = Ω)
    (frame : Td_retag_d native ω A S U V e o T U' V')
    (alphabet : Td_alphabet_d S U V) (tagged : Td_alphabet_d T U' V')
    (empty : ∀ x, ¬ M.mem x z) (ff : Fn0_d Ω A.val f)
    (good : Td_fixed_gp_d hZF Ω z c X A.val T.val f) : Td_fixed_gp_d hZF Ω z c X A.val S.val f := by
  let v : Fin 10 → (smdl_structure_l I (R := R) source.1.2.1).Domain :=
    fun i => [ω,A,S,U,V,e,o,T,U',V'].get i
  have frame : Td_retag_d native (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) := frame
  obtain ⟨ρ,γ,rank,lower,ordinal,B,Q,G,E,tree,owned,copy,bound,branches⟩ := good
  refine ⟨ρ,γ,rank,lower,ordinal,B,Q,G,E,tree,owned,copy,bound,?_⟩
  intro b wf
  obtain ⟨d,N,W,P,j,S',Y,F,U₀,V₀,target,nt,cone,leg,image,space,closed,letters,projection,_,fixedA,pointA,low⟩ := branches b wf
  have map := cone.elementary z j c X R leg (tree.root z empty) source.1
  have native' := map.native_models_l hZF hΩ source.1 target.1 native
  obtain ⟨images,points⟩ := Classical.axiomOfChoice (fun i : Fin 10 => map.1.1.2.2 (v i).val (v i).property)
  let w : Fin 10 → (smdl_structure_l I (R := W) target.1.2.1).Domain := fun i => ⟨images i,(points i).1⟩
  have iw i : Rd_entry_d (v i).val (w i).val j := (points i).2
  have omega := map.omega_l I hZF hΩ trans nt source target (eqω ▸ ω.property)
  have iw0 : Rd_entry_d ω.val (w 0).val j := iw 0
  have eq0 : (w 0).val = Ω := map.1.1.1.2 Ω (w 0).val Ω (eqω ▸ iw0) omega
  have targetω : (smdl_structure_l I (R := W) target.1.2.1).IsOmega (w 0) := by
    let η := (⟨fun _ => ω,fun _ => ω⟩ : Env _ 1)
    let θ := (⟨fun _ => w 0,fun _ => w 0⟩ : Env _ 1)
    exact (Formula.satisfies_isOmega_iff θ .newest).mp
      ((smap_source_l I hZF hΩ source.1 target.1 map (Formula.isOmega .newest)
        (by simp -implicitDefEqProofs) η θ (fun _ => iw 0)).mp
          ((Formula.satisfies_isOmega_iff η .newest).mpr hw))
  obtain ⟨r⟩ := frame.native_map_l hZF hΩ source.1 target.1 map native native' iw
  let old : Fin 3 → Fin 10 := fun i => [2,3,4].get i
  let tag : Fin 3 → Fin 10 := fun i => [7,8,9].get i
  have alphabet' := Td_alphabet_d.native_map_l hZF hΩ source.1 target.1 map native.1 native'.1
    (v := fun i => v (old i)) (w := fun i => w (old i)) alphabet (fun i => iw (old i))
  have tagged' := Td_alphabet_d.native_map_l hZF hΩ source.1 target.1 map native.1 native'.1
    (v := fun i => v (tag i)) (w := fun i => w (tag i)) tagged (fun i => iw (tag i))
  have inj : Function.Injective (Subtype.val : (smdl_structure_l I (R := W) target.1.2.1).Domain → M.Domain) :=
    fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I target nt
  have alphabet' := Td_alphabet_d.ground_l native' hZF Subtype.val inj full alphabet' r.space r.source r.pair r.triple
  have tagged' := Td_alphabet_d.ground_l native' hZF Subtype.val inj full tagged' r.space' (r.tree_l native') r.pair' r.triple'
  obtain ⟨r'⟩ := r.image_l native' hZF Subtype.val inj full targetω (eq0.symm ▸ hΩ)
  have eqT : (w 7).val = S' := map.1.1.1.2 _ _ _ (iw 7) image
  obtain ⟨eqU,eqV⟩ := (eqT ▸ tagged').ext_l hZF.1 letters
  change (w 8).val = U₀ at eqU
  change (w 9).val = V₀ at eqV
  have sp : Fseq_space_d I Ω r'.Y' r'.F' := by simpa only [eq0] using! r'.space'
  have tr : Tree_d r'.F' S' := by simpa only [eqT] using r'.tree_l hZF
  have copied : Td_projection_d hZF (w 0).val (w 8).val (w 9).val r'.Y' r'.F' (w 7).val f := by
    have p := projection.space_l hZF hΩ space sp tr
    simpa only [eq0,eqT,eqU,eqV] using p
  have p := r'.projection_l hZF (eq0.symm ▸ hΩ) (by simpa only [eq0] using ff) copied
  exact ⟨d,N,W,P,j,(w 2).val,r'.Y,r'.F,(w 3).val,(w 4).val,
    target,nt,cone,leg,iw 2,by simpa only [eq0] using! r'.space,r'.source,alphabet',
    by simpa only [eq0] using p,map,fixedA,pointA,low⟩

end YesMetaZFC.SetTheory.LargeCardinal
