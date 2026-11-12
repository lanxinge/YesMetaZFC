import YesMetaZFC.Model.Forcing.Collapse.ProductCoordinates
import YesMetaZFC.Model.Forcing.Automorphism.RealSetName
import YesMetaZFC.Model.Forcing.Homogeneous.HOD
import YesMetaZFC.Model.Forcing.Ground.FilterSet
import YesMetaZFC.Model.Forcing.Ground.SubsetOrder
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.Model.Forcing.Collapse.ProductRealCollapse
import YesMetaZFC.Model.Forcing.Truth.ClosedTruth

/-! # 两条有限条件实际产生坍缩自同构

交换由原两条条件编码，在它们共同定义域外固定每个字母。
同一作用保持任意内部长度、反向包含和空条件，平方为恒等。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fs_val_total_l {p q X i x : M.Domain}
    (hp : ∀ i a, Entry_d M i a p → M.mem a X)
    (hq : ∀ i a, Entry_d M i a q → M.mem a X) (hx : M.mem x X) :
    ∃ y, M.mem y X ∧ Fs_val_d p q i x y := by
  classical
  by_cases h : ∃ a b, Entry_d M i a p ∧ Entry_d M i b q
  · obtain ⟨a,b,ia,ib⟩ := h
    by_cases ha : x = a
    · exact ⟨b,hq i b ib,Or.inl ⟨a,b,ia,ib,Or.inl ⟨ha,rfl⟩⟩⟩
    · by_cases hb : x = b
      · exact ⟨a,hp i a ia,Or.inl ⟨a,b,ia,ib,Or.inr (Or.inl ⟨hb,rfl⟩)⟩⟩
      · exact ⟨x,hx,Or.inl ⟨a,b,ia,ib,Or.inr (Or.inr ⟨ha,hb,rfl⟩)⟩⟩
  · exact ⟨x,hx,Or.inr ⟨h,rfl⟩⟩

theorem Fs_swap_d.unique_l (hE : Extensional M) {p q s t u : M.Domain}
    (h : Fs_swap_d p q s t) (k : Fs_swap_d p q s u) : t = u := by
  have sub {t u} (h : Fs_swap_d p q s t) (k : Fs_swap_d p q s u) z (hz : M.mem z t) : M.mem z u := by
    obtain ⟨i,y,c⟩ := h.1 z hz
    obtain ⟨v,cv,hv⟩ := (k.2 i y).mpr ((h.2 i y).mp ⟨z,c,hz⟩)
    exact kpair_unique_l M hE cv c ▸ hv
  exact hE.eq_of_same_members t u fun z => ⟨sub h k z,sub k h z⟩

omit hZF in
theorem Fs_swap_d.mono_l {p q s t u v : M.Domain}
    (h : Fs_swap_d p q s t) (k : Fs_swap_d p q u v)
    (sub : M.MemberSubset s u) (hE : Extensional M) : M.MemberSubset t v := by
  intro z hz
  obtain ⟨i,y,c⟩ := h.1 z hz
  obtain ⟨x,⟨w,cw,hw⟩,xy⟩ := (h.2 i y).mp ⟨z,c,hz⟩
  obtain ⟨z',cz,hz'⟩ := (k.2 i y).mpr ⟨x,⟨w,cw,sub w hw⟩,xy⟩
  exact kpair_unique_l M hE cz c ▸ hz'

/-- 单次作用的图由替换取得；这里保留任意集合长度，尚不用内部有限性。 -/
theorem fs_swap_exists_l {ω X p q n s : M.Domain}
    (hp : Pfn_d I ω X p) (hq : Pfn_d I ω X q) (hs : M.IsSetFunctionFromTo I s n X) :
    ∃ t, M.IsSetFunctionFromTo I t n X ∧ Fs_swap_d p q s t := by
  let ρ : Env M 3 := ⟨fun i => [p,q,s].get i,fun _ => p⟩
  let φ : BinarySchema 3 := { body := .existsE (.conj
    (entry_m (.bound 2) .newest (.bound 5))
    (fs_val_m (.bound 3) (.bound 4) (.bound 2) .newest (.bound 1))) }
  have sat i y : φ.denote ρ i y ↔ ∃ x, Entry_d M i x s ∧ Fs_val_d p q i x y := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      entry_sat_l M hZF.1,fs_val_sat_l hZF.1]
    rfl
  obtain ⟨t,ft,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := X)
    (by
      intro i hi
      obtain ⟨x,hx,ix⟩ := hs.2.2 i hi
      obtain ⟨y,_,xy⟩ := fs_val_total_l (fun i a ia => (hp.2 i a ia).2)
        (fun i a ia => (hq.2 i a ia).2) hx
      exact ⟨y,(sat i y).mpr ⟨x,ix,xy⟩⟩)
    (by
      intro i _ y z hy hz
      obtain ⟨x,ix,xy⟩ := (sat i y).mp hy
      obtain ⟨a,ia,az⟩ := (sat i z).mp hz
      have eq := hs.1.2 i x a ix ia
      subst a
      exact Fs_val_d.unique_l hp.1.2 hq.1.2 xy az)
    (by
      intro i y _ hy
      obtain ⟨x,ix,xy⟩ := (sat i y).mp hy
      obtain ⟨z,hz,xz⟩ := fs_val_total_l (fun i a ia => (hp.2 i a ia).2)
        (fun i a ia => (hq.2 i a ia).2) (hs.output_mem_of_pairMember ix)
      exact (Fs_val_d.unique_l hp.1.2 hq.1.2 xz xy) ▸ hz)
  refine ⟨t,ft,ft.1.1,fun i y => (graph i y).trans ?_⟩
  rw [sat]
  exact ⟨And.right,fun h => ⟨h.elim fun _ hx => hs.input_mem_of_pairMember hx.1,h⟩⟩

theorem Fs_swap_d.inverse_l {ω X p q n s t : M.Domain}
    (hp : Pfn_d I ω X p) (hq : Pfn_d I ω X q)
    (hs : M.IsSetFunctionFromTo I s n X) (h : Fs_swap_d p q s t) : Fs_swap_d p q t s := by
  refine ⟨hs.1.1,fun i x => ⟨?_,?_⟩⟩
  · intro ix
    obtain ⟨y,_,xy⟩ := fs_val_total_l (fun i a ia => (hp.2 i a ia).2)
      (fun i a ia => (hq.2 i a ia).2) (hs.output_mem_of_pairMember ix)
    exact ⟨y,(h.2 i y).mpr ⟨x,ix,xy⟩,xy.symm_l⟩
  · rintro ⟨y,iy,yx⟩
    obtain ⟨z,iz,zy⟩ := (h.2 i y).mp iy
    exact (Fs_val_d.unique_l hp.1.2 hq.1.2 zy.symm_l yx) ▸ iz

/-- 内部有限初段条件上的实际自同构，完整保存每条条件的长度。 -/
theorem fseq_swap_l {ω X B R p q : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X B)
    (order : ∀ s t, Entry_d M s t R ↔ M.mem s B ∧ M.mem t B ∧ M.MemberSubset t s)
    (hp : M.mem p B) (hq : M.mem q B) :
    ∃ F, Aut_d M B R B F ∧
      (∀ s t, Entry_d M s t F ↔ M.mem s B ∧ Fs_swap_d p q s t) ∧
      (∀ s t, Entry_d M s t F → Entry_d M t s F) ∧
      (∀ n s t, M.IsSetFunctionFromTo I s n X → Entry_d M s t F → M.IsSetFunctionFromTo I t n X) ∧
      ∀ e, (∀ x, ¬ M.mem x e) → Entry_d M e e F := by
  have pfn {s} (hs : M.mem s B) : Pfn_d I ω X s := by
    obtain ⟨n,hn,fs⟩ := (space s).mp hs
    exact ⟨fs.1,fun i x ix => ⟨hw.transitive (ZF.modelsKP hZF) n hn i
      (fs.input_mem_of_pairMember ix),fs.output_mem_of_pairMember ix⟩⟩
  have swap := fun {n s} (fs : M.IsSetFunctionFromTo I s n X) =>
    fs_swap_exists_l hZF (pfn hp) (pfn hq) fs
  have inverse := fun {n s t} (fs : M.IsSetFunctionFromTo I s n X) (h : Fs_swap_d p q s t) =>
    h.inverse_l hZF (pfn hp) (pfn hq) fs
  let ρ : Env M 2 := ⟨fun i => [p,q].get i,fun _ => p⟩
  let φ : BinarySchema 2 := { body := fs_swap_m (.bound 2) (.bound 3) (.bound 1) .newest }
  have sat s t : φ.denote ρ s t ↔ Fs_swap_d p q s t := fs_swap_sat_l hZF.1 ..
  have pick s (hs : M.mem s B) : ∃ t, M.mem t B ∧ Fs_swap_d p q s t := by
    obtain ⟨n,hn,fs⟩ := (space s).mp hs
    obtain ⟨t,ft,st⟩ := swap fs
    exact ⟨t,(space t).mpr ⟨n,hn,ft⟩,st⟩
  obtain ⟨F,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := B) (target := B)
    (fun s hs => (pick s hs).elim fun t ht => ⟨t,(sat s t).mpr ht.2⟩)
    (fun _ _ _ _ hs ht => ((sat ..).mp hs).unique_l hZF.1 ((sat ..).mp ht))
    (by
      intro s t hs st
      obtain ⟨u,hu,su⟩ := pick s hs
      exact su.unique_l hZF.1 ((sat s t).mp st) ▸ hu)
  have edges s t : Entry_d M s t F ↔ M.mem s B ∧ Fs_swap_d p q s t :=
    (graph s t).trans (and_congr_right fun _ => sat s t)
  have inv {s t} (st : Entry_d M s t F) : Fs_swap_d p q t s := by
    obtain ⟨n,_,fs⟩ := (space s).mp (fn.input_mem_of_pairMember st)
    exact inverse fs ((edges s t).mp st).2
  have aut : Aut_d M B R B F := by
    refine aut_of_bij_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ⟨⟨fn,?_⟩,?_⟩ ?_ ?_
    · intro s t u su tu
      exact (inv su).unique_l hZF.1 (inv tu)
    · intro t ht
      obtain ⟨s,hs,ts⟩ := pick t ht
      obtain ⟨n,_,ft⟩ := (space t).mp ht
      exact ⟨s,hs,(edges s t).mpr ⟨hs,inverse ft ts⟩⟩
    · intro s t u v su tv
      rw [order s t,order u v]
      exact ⟨fun h => ⟨fn.output_mem_of_pairMember su,fn.output_mem_of_pairMember tv,
        ((edges t v).mp tv).2.mono_l ((edges s u).mp su).2 h.2.2 hZF.1⟩,
        fun h => ⟨fn.input_mem_of_pairMember su,fn.input_mem_of_pairMember tv,
          (inv tv).mono_l (inv su) h.2.2 hZF.1⟩⟩
    · intro s t st
      exact iff_of_false (fun e => KP.mem_irrefl_d (ZF.modelsKP hZF) B (e ▸ fn.input_mem_of_pairMember st))
        (fun e => KP.mem_irrefl_d (ZF.modelsKP hZF) B (e ▸ fn.output_mem_of_pairMember st))
  refine ⟨F,aut,edges,fun s t st => (edges t s).mpr ⟨fn.output_mem_of_pairMember st,inv st⟩,?_,?_⟩
  · intro n s t fs st
    obtain ⟨u,fu,su⟩ := swap fs
    exact su.unique_l hZF.1 ((edges s t).mp st).2 ▸ fu
  · intro e he
    have seq := Structure.IsSequenceOfLength.empty I he
    have fe : M.IsSetFunctionFromTo I e e X := ⟨seq.2.1,seq.2.2,fun x hx => (he x hx).elim⟩
    obtain ⟨o,ho,hoω⟩ := hw.1.1
    have eq := hZF.1.eq_of_same_members o e (fun x => iff_of_false (ho x) (he x))
    refine (edges e e).mpr ⟨(space e).mpr ⟨e,eq ▸ hoω,fe⟩,seq.2.1.1,?_⟩
    exact fun i y => ⟨fun ⟨v,_,hv⟩ => (he v hv).elim,fun ⟨_,⟨v,_,hv⟩,_⟩ => (he v hv).elim⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 有限初段坍缩的弱齐性

在公共位置交换两条条件的值后，所得条件逐项相容。
内部自然数长度可比，故较长条件就是共同加强；无需字母表的基数性。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fseq_whom_l {ω X B R : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X B)
    (order : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p) :
    Whom_d M B R B := by
  intro p q hp _ hq _
  obtain ⟨n,hn,fp⟩ := (space p).mp hp
  obtain ⟨m,hm,fq⟩ := (space q).mp hq
  obtain ⟨F,aut,edges,_,lengths,_⟩ := fseq_swap_l hZF hw space order hp hq
  obtain ⟨s,ps⟩ := aut.total p hp
  have hs := (aut.domain p s ps).2
  have fs := lengths n p s fp ps
  have agree i x y (ix : Entry_d M i x s) (iy : Entry_d M i y q) : x = y := by
    obtain ⟨a,ia,ax⟩ := ((edges p s).mp ps).2.2 i x |>.mp ix
    exact Fs_val_d.unique_l fp.1.2 fq.1.2 ax (Or.inl ⟨a,y,ia,iy,Or.inl ⟨rfl,rfl⟩⟩)
  have sub {a b k l} (fa : M.IsSetFunctionFromTo I a k X) (fb : M.IsSetFunctionFromTo I b l X)
      (agree : ∀ i x y, Entry_d M i x a → Entry_d M i y b → x = y)
      (kl : M.MemberSubset k l) : M.MemberSubset a b := by
    intro z hz
    obtain ⟨i,x,c⟩ := fa.1.1 z hz
    have ix : Entry_d M i x a := ⟨z,c,hz⟩
    obtain ⟨y,_,iy⟩ := fb.2.2 i (kl i (fa.input_mem_of_pairMember ix))
    have eq := agree i x y ix iy
    obtain ⟨v,cv,hv⟩ := eq.symm ▸ iy
    exact (I).unique cv c ▸ hv
  have compare : M.MemberSubset n m ∨ M.MemberSubset m n := by
    rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn m hm with eq | lt | gt
    · exact Or.inl fun i hi => (eq i).mp hi
    · exact Or.inl ((hw.members_areOrdinals (ZF.modelsKP hZF) m hm).transitive n lt)
    · exact Or.inr ((hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive m gt)
  refine ⟨F,s,aut,ps,?_⟩
  rcases compare with nm | mn
  · exact ⟨q,subset_below_l hZF order hs hq (sub fs fq agree nm),
      (order q q).mpr ⟨hq,hq,fun _ h => h⟩⟩
  · exact ⟨s,subset_below_l hZF order hs hs (fun _ h => h),
      (order s q).mpr ⟨hs,hq,sub fq fs (fun i x y ix iy => (agree i y x iy ix).symm) mn⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 泛型坍缩满足指定有限条件且保持扩张

先从同一泛型中取得足够长的原条件，再在给定条件的有限定义域内交换各位置的值。
新泛型接受指定条件，运输名字与原名字给出同一扩张中的对应值。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

/-- 原泛型中确有覆盖给定有限定义域的条件；不使用外部有限枚举。 -/
theorem fseq_generic_cover_l {ω X B R p : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X B)
    (order : ∀ s t, Entry_d M s t R ↔ M.mem s B ∧ M.mem t B ∧ M.MemberSubset t s)
    {G : M.Domain → Prop} (generic : Generic_d M B R B G) (hp : M.mem p B) :
    ∃ q, G q ∧ ∀ i x, Entry_d M i x p → ∃ y, Entry_d M i y q := by
  classical
  obtain ⟨n,hn,fp⟩ := (space p).mp hp
  by_cases inh : ∃ x, M.mem x X
  · obtain ⟨q,hq,y,ny⟩ := fseq_generic_input_l hZF hw space order generic inh hn
    obtain ⟨m,hm,fq⟩ := (space q).mp (generic.proper q hq).1
    refine ⟨q,hq,fun i x ix => ?_⟩
    exact (fq.2.2 i ((hw.members_areOrdinals (ZF.modelsKP hZF) m hm).transitive n
      (fq.input_mem_of_pairMember ny) i (fp.input_mem_of_pairMember ix))).imp fun _ hy => hy.2
  · obtain ⟨q,hq⟩ := generic.inhabited
    exact ⟨q,hq,fun _ x ix => (inh ⟨x,fp.output_mem_of_pairMember ix⟩).elim⟩

/-- 实际有限交换令新泛型含指定条件；共同定义域外的每个位置逐字固定。 -/
theorem fseq_retarget_l {ω X B R p : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X B) (O : Cond_order_d M B R B)
    (order : ∀ s t, Entry_d M s t R ↔ M.mem s B ∧ M.mem t B ∧ M.MemberSubset t s)
    {G : M.Domain → Prop} (generic : Generic_d M B R B G) (hp : M.mem p B) :
    ∃ F, Aut_d M B R B F ∧ Generic_d M B R B (Pull_generic_d M F G) ∧
      Pull_generic_d M F G p ∧
      (∀ s t i x, Entry_d M s t F → ¬ (∃ y, Entry_d M i y p) →
        (Entry_d M i x t ↔ Entry_d M i x s)) ∧
      ∃ e : (extension_l M hZF B R B (Pull_generic_d M F G)).Domain →
          (extension_l M hZF B R B G).Domain,
        (∀ a b, (extension_l M hZF B R B (Pull_generic_d M F G)).mem a b ↔
          (extension_l M hZF B R B G).mem (e a) (e b)) ∧
        Function.Injective e ∧ Function.Surjective e ∧
        (∀ x a, Gval_d M B R B (Pull_generic_d M F G) x a ↔ Gval_d M B R B G x (e a)) ∧
        ∀ a s t, Qval_d M B R B (Pull_generic_d M F G) s a → Nmap_d M F s t →
          Qval_d M B R B G t (e a) := by
  obtain ⟨q,hq,cover⟩ := fseq_generic_cover_l hZF hw space order generic hp
  obtain ⟨F,aut,edges,inverse,_,_⟩ := fseq_swap_l hZF hw space order (generic.proper q hq).1 hp
  obtain ⟨t,qt⟩ := aut.total q (generic.proper q hq).1
  have swapped := ((edges q t).mp qt).2
  have sub : M.MemberSubset p t := by
    intro z hz
    obtain ⟨n,_,fp⟩ := (space p).mp hp
    obtain ⟨i,x,c⟩ := fp.1.1 z hz
    have ix : Entry_d M i x p := ⟨z,c,hz⟩
    obtain ⟨y,iy⟩ := cover i x ix
    obtain ⟨z',cz,hz'⟩ := (swapped.2 i x).mpr
      ⟨y,iy,Or.inl ⟨y,x,iy,ix,Or.inl ⟨rfl,rfl⟩⟩⟩
    exact (I).unique cz c ▸ hz'
  have reverse := inverse q t qt
  obtain ⟨gen,e,mem,inj,onto,ground,values⟩ := aut_extension_l O hZF aut generic
  refine ⟨F,aut,gen,gen.upward t p ⟨q,reverse,hq⟩ hp
    ((order t p).mpr ⟨(aut.domain q t qt).2,hp,sub⟩),?_,e,mem,inj,onto,ground,values⟩
  intro s t i x st outside
  apply ((edges s t).mp st).2.2 i x |>.trans
  constructor
  · rintro ⟨y,iy,⟨a,b,_,ib,_⟩ | ⟨_,eq⟩⟩
    · exact (outside ⟨b,ib⟩).elim
    · exact eq.symm ▸ iy
  · intro ix
    exact ⟨x,ix,Or.inr ⟨fun ⟨_,b,_,ib⟩ => outside ⟨b,ib⟩,rfl⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 在原地模型中选定有限交换图

扩张中的有限条件由地条件满覆盖。先取原泛型中的足够长条件，
在地模型内构造交换图，再搬运同一自同构，保留可供背景分离的地参数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))

theorem fseq_ground_retarget_l (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {ω X B R p : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (space : Fseq_space_d I ω X B) (O : Cond_order_d M B R B)
    (order : ∀ s t, Entry_d M s t R ↔ M.mem s B ∧ M.mem t B ∧ M.MemberSubset t s)
    {G : M.Domain → Prop} (generic : Generic_d N (e B) (e R) (e B) (Em_generic_d e G)) (hp : M.mem p B) :
    ∃ F, Aut_d M B R B F ∧
      Generic_d N (e B) (e R) (e B) (Em_generic_d e (Pull_generic_d M F G)) ∧
      Pull_generic_d M F G p ∧
      ∃ v : (extension_l N hN (e B) (e R) (e B) (Em_generic_d e (Pull_generic_d M F G))).Domain →
        (extension_l N hN (e B) (e R) (e B) (Em_generic_d e G)).Domain,
        (∀ a b, (extension_l N hN (e B) (e R) (e B) (Em_generic_d e (Pull_generic_d M F G))).mem a b ↔
          (extension_l N hN (e B) (e R) (e B) (Em_generic_d e G)).mem (v a) (v b)) ∧
        Function.Injective v ∧ Function.Surjective v ∧
        (∀ x a, Gval_d N (e B) (e R) (e B) (Em_generic_d e (Pull_generic_d M F G)) x a ↔
          Gval_d N (e B) (e R) (e B) (Em_generic_d e G) x (v a)) := by
  have O' := image_cond_order_l (ZF.modelsKP hM) hN.1 e inj full O
  have order' := image_subset_order_l (ZF.modelsKP hM) hN.1 e inj full order
  have space' := image_fseq_l hM hN e inj full hw hw' space
  obtain ⟨q,⟨q₀,hq,rfl⟩,cover⟩ := fseq_generic_cover_l hN hw' space' order' generic
    ((image_member_l e inj full).mpr hp)
  have hqB := (image_member_l e inj full).mp (generic.proper (e q₀) ⟨q₀,hq,rfl⟩).1
  have entry := image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  obtain ⟨F,aut,edges,inverse,_,_⟩ := fseq_swap_l hM hw space order hqB hp
  obtain ⟨t,qt⟩ := aut.total q₀ hqB
  have sub : M.MemberSubset p t := by
    intro z hz
    obtain ⟨n,_,fp⟩ := (space p).mp hp
    obtain ⟨i,x,c⟩ := fp.1.1 z hz
    have ix : Entry_d M i x p := ⟨z,c,hz⟩
    obtain ⟨y,iy⟩ := cover (e i) (e x) ((entry i x p).mp ix)
    obtain ⟨m,_,fq⟩ := (space q₀).mp hqB
    obtain ⟨i',a,ia,ii,rfl⟩ := (image_entries_l e full fq.1.1 (e i) y).mp iy
    have eq := inj ii
    subst i'
    obtain ⟨z',cz,hz'⟩ := ((edges q₀ t).mp qt).2.2 i x |>.mpr
      ⟨a,ia,Or.inl ⟨a,x,ia,ix,Or.inl ⟨rfl,rfl⟩⟩⟩
    exact (I).unique cz c ▸ hz'
  have auto := image_aut_l (ZF.modelsKP hM) (ZF.modelsKP hN) e inj full aut
  have result := aut_extension_l O' hN auto generic
  rw [image_pull_l e inj full aut G] at result
  obtain ⟨gen,v,vm,vi,vo,vg,_⟩ := result
  have accepted := gen.upward (e t) (e p) ⟨t,⟨q₀,inverse q₀ t qt,hq⟩,rfl⟩
    ((image_member_l e inj full).mpr hp)
    ((entry t p R).mp ((order t p).mpr ⟨(aut.domain q₀ t qt).2,hp,sub⟩))
  obtain ⟨p',accepted,eq⟩ := accepted
  exact ⟨F,aut,gen,inj eq ▸ accepted,v,vm,vi,vo,vg⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 一个尾坐标上的实际乘积自同构

指定坐标使用两条原部分条件给出的逐位置值交换，所有其他坐标逐行不动。
原集合替代构造整个条件图；长度保持、平方恒等及顺序保持均从同一图证明。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def Fc_row_d (i a b k s t : M.Domain) : Prop := (k = i ∧ Fs_swap_d a b s t) ∨ (k ≠ i ∧ t = s)
def fc_row_m {d} (i a b k s t : Term d) : Formula 1 d := set[d] ⟪
  (⌜k⌝ₛ = ⌜i⌝ₛ ∧ ⌜fs_swap_m⌝ₚ(⌜a⌝ₛ,⌜b⌝ₛ,⌜s⌝ₛ,⌜t⌝ₛ)) ∨ (⌜k⌝ₛ ≠ ⌜i⌝ₛ ∧ ⌜t⌝ₛ = ⌜s⌝ₛ)⟫
derive_free_closed fc_row_m

def Fc_swap_d (i a b s t : M.Domain) : Prop :=
  (∀ v, M.mem v t → ∃ k x, KPair_d M v k x) ∧
    ∀ k x, Entry_d M k x t ↔ ∃ y, Entry_d M k y s ∧ Fc_row_d i a b k y x
def fc_swap_m {d} (i a b s t : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isRelation kpair_convention_l⌝ₚ(⌜t⌝ₛ) ∧
    (∀ k x, ⌜entry_m⌝ₚ(k,x,⌜t⌝ₛ) ↔ ∃ y, ⌜entry_m⌝ₚ(k,y,⌜s⌝ₛ) ∧ ⌜fc_row_m⌝ₚ(⌜i⌝ₛ,⌜a⌝ₛ,⌜b⌝ₛ,k,y,x))⟫
derive_free_closed fc_swap_m

theorem fc_row_sat_l (hE : Extensional M) {d} (ρ : Env M d) (i a b k s t : Term d) :
    Formula.satisfies ρ (fc_row_m i a b k s t) ↔
      Fc_row_d (i.eval ρ) (a.eval ρ) (b.eval ρ) (k.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [fc_row_m,Fc_row_d,Formula.satisfies_disj_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE,Formula.extensionalNe,Formula.satisfies_neg_iff,fs_swap_sat_l hE]

theorem fc_swap_sat_l (hE : Extensional M) {d} (ρ : Env M d) (i a b s t : Term d) :
    Formula.satisfies ρ (fc_swap_m i a b s t) ↔ Fc_swap_d (i.eval ρ) (a.eval ρ) (b.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [fc_swap_m,Fc_swap_d,Formula.isRelation,kpair_convention_l,Formula.satisfies_conj_iff,
    Formula.satisfies_forallMem_iff,Formula.satisfies_exists_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,kpair_sat_l M hE,entry_sat_l M hE,fc_row_sat_l hE,
    Definitional.Term.eval_weaken]
  rfl

theorem Fc_row_d.unique_l (hE : Extensional M) {i a b k s t u : M.Domain}
    (h : Fc_row_d i a b k s t) (g : Fc_row_d i a b k s u) : t = u := by
  rcases h with ⟨eq,h⟩ | ⟨ne,h⟩ <;> rcases g with ⟨eq',g⟩ | ⟨ne',g⟩
  · exact h.unique_l hE g
  · exact (ne' eq).elim
  · exact (ne eq').elim
  · exact h.trans g.symm

theorem Fc_swap_d.unique_l (hE : Extensional M) {i a b s t u : M.Domain}
    (h : Fc_swap_d i a b s t) (g : Fc_swap_d i a b s u) : t = u := by
  apply entry_ext_l M hE h.1 g.1
  intro k x
  rw [h.2,g.2]

variable (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Fc_swap_d.le_l {ω A i a b m s t u v : M.Domain}
    (fs : Fp_at_d I ω A m s) (ft : Fp_at_d I ω A m t)
    (st : Fc_swap_d i a b s t) (uv : Fc_swap_d i a b u v) (le : Fp_le_d I s u) : Fp_le_d I t v := by
  intro k z kz
  obtain ⟨y,ky,yz⟩ := (uv.2 k z).mp kz
  obtain ⟨w,kw,yw⟩ := le k y ky
  obtain ⟨r,kr⟩ := (ft.domain k).mp ((fs.domain k).mpr ⟨w,kw⟩)
  obtain ⟨w',kw',wr⟩ := (st.2 k r).mp kr
  have eq := fs.function.2 k w' w kw' kw
  subst w'
  refine ⟨r,kr,?_⟩
  rcases yz with ⟨eq,yz⟩ | ⟨ne,yz⟩ <;> rcases wr with ⟨eq',wr⟩ | ⟨ne',wr⟩
  · exact yz.mono_l wr yw hZF.1
  · exact (ne' eq).elim
  · exact (ne eq').elim
  · exact yz.symm ▸ wr.symm ▸ yw

variable {ω A i κ a b : M.Domain}
  (fa : M.IsSetFunction (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) A) (alphabet : Entry_d M i κ A)
  (pa : Pfn_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω κ a)
  (pb : Pfn_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω κ b)
include fa alphabet pa pb

theorem fc_swap_exists_l {m s : M.Domain} (fs : Fp_at_d I ω A m s) :
    ∃ t, Fp_at_d I ω A m t ∧ Fc_swap_d i a b s t := by
  have row {k y} (ky : Entry_d M k y s) : ∃ z, Fc_row_d i a b k y z := by
    rcases Classical.em (k = i) with eq | ne
    · subst k
      obtain ⟨δ,n,iδ,_,fy⟩ := fs.coordinates i y ky
      have eq := fa.2 i δ κ iδ alphabet
      obtain ⟨z,_,yz⟩ := fs_swap_exists_l hZF pa pb (eq ▸ fy)
      exact ⟨z,Or.inl ⟨rfl,yz⟩⟩
    · exact ⟨y,Or.inr ⟨ne,rfl⟩⟩
  let ρ : Env M 4 := ⟨fun j => [i,a,b,s].get j,fun _ => i⟩
  let φ : BinarySchema 4 := { body := .existsE (.conj (entry_m (.bound 2) .newest (.bound 6))
    (fc_row_m (.bound 3) (.bound 4) (.bound 5) (.bound 2) .newest (.bound 1))) }
  have sat k z : φ.denote ρ k z ↔ ∃ y, Entry_d M k y s ∧ Fc_row_d i a b k y z := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,entry_sat_l M hZF.1,fc_row_sat_l hZF.1]
    rfl
  have total k (hk : M.mem k m) : ∃ z, φ.denote ρ k z := by
    obtain ⟨y,ky⟩ := (fs.domain k).mp hk
    obtain ⟨z,yz⟩ := row ky
    exact ⟨z,(sat k z).mpr ⟨y,ky,yz⟩⟩
  have unique k z u (hz : φ.denote ρ k z) (hu : φ.denote ρ k u) : z = u := by
    obtain ⟨y,ky,yz⟩ := (sat k z).mp hz
    obtain ⟨y',ky',yu⟩ := (sat k u).mp hu
    exact yz.unique_l hZF.1 (fs.function.2 k y' y ky' ky ▸ yu)
  obtain ⟨V,range⟩ := ZF.exists_functionalImage hZF φ ρ m total unique
  obtain ⟨t,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total
    (fun k _ => unique k) (fun k z hk hz => (range z).mpr ⟨k,hk,hz⟩)
  have entries k z : Entry_d M k z t ↔ ∃ y, Entry_d M k y s ∧ Fc_row_d i a b k y z :=
    (graph k z).trans ((and_congr_right fun _ => sat k z).trans
      ⟨And.right,fun h => ⟨h.elim fun y hy => (fs.domain k).mpr ⟨y,hy.1⟩,h⟩⟩)
  refine ⟨t,⟨fn.1,fn.2.1,?_⟩,fn.1.1,entries⟩
  intro k z kz
  obtain ⟨y,ky,yz⟩ := (entries k z).mp kz
  obtain ⟨δ,n,kδ,hn,fy⟩ := fs.coordinates k y ky
  rcases yz with ⟨eq,swap⟩ | ⟨_,eq⟩
  · subst k
    have eqδ := fa.2 i δ κ kδ alphabet
    subst δ
    obtain ⟨u,fu,yu⟩ := fs_swap_exists_l hZF pa pb fy
    exact ⟨κ,n,alphabet,hn,yu.unique_l hZF.1 swap ▸ fu⟩
  · exact ⟨δ,n,kδ,hn,eq.symm ▸ fy⟩

theorem Fc_swap_d.inverse_l {m s t : M.Domain} (fs : Fp_at_d I ω A m s) (h : Fc_swap_d i a b s t) :
    Fc_swap_d i a b t s := by
  have reverse {k y z} (ky : Entry_d M k y s) (yz : Fc_row_d i a b k y z) : Fc_row_d i a b k z y := by
    rcases yz with ⟨eq,swap⟩ | ⟨ne,eq⟩
    · subst k
      obtain ⟨δ,n,iδ,_,fy⟩ := fs.coordinates i y ky
      exact Or.inl ⟨rfl,swap.inverse_l hZF pa pb (fa.2 i δ κ iδ alphabet ▸ fy)⟩
    · exact Or.inr ⟨ne,eq.symm⟩
  refine ⟨fs.function.1,fun k y => ⟨?_,?_⟩⟩
  · intro ky
    obtain ⟨t',ft',st'⟩ := fc_swap_exists_l hZF fa alphabet pa pb fs
    obtain ⟨z,kz⟩ := (ft'.domain k).mp ((fs.domain k).mpr ⟨y,ky⟩)
    obtain ⟨y',ky',yz⟩ := (st'.2 k z).mp kz
    have eq := fs.function.2 k y' y ky' ky
    subst y'
    exact ⟨z,(h.2 k z).mpr ⟨y,ky,yz⟩,reverse ky yz⟩
  · rintro ⟨z,kz,zy⟩
    obtain ⟨u,ku,uz⟩ := (h.2 k z).mp kz
    have eq := (reverse ku uz).unique_l hZF.1 zy
    exact eq ▸ ku

theorem fp_coordinate_swap_l {P R : M.Domain} (product : Fp_product_d hZF ω A P R) :
    ∃ F, Fp_aut_d I P R F ∧
      (∀ s t, Entry_d M s t F ↔ M.mem s P ∧ Fc_swap_d i a b s t) ∧
      (∀ s t, Entry_d M s t F → Entry_d M t s F) ∧
      ∀ n, ¬ M.mem i n → Fp_tail_d I n P R F := by
  let ρ : Env M 3 := ⟨fun k => [i,a,b].get k,fun _ => i⟩
  let φ : BinarySchema 3 := { body := fc_swap_m (.bound 2) (.bound 3) (.bound 4) (.bound 1) .newest }
  have sat s t : φ.denote ρ s t ↔ Fc_swap_d i a b s t := fc_swap_sat_l hZF.1 ..
  have pick s (hs : M.mem s P) : ∃ t, M.mem t P ∧ Fc_swap_d i a b s t := by
    obtain ⟨m,hm,fs⟩ := (product.conditions s).mp hs
    obtain ⟨t,ft,st⟩ := fc_swap_exists_l hZF fa alphabet pa pb fs
    exact ⟨t,(product.conditions t).mpr ⟨m,hm,ft⟩,st⟩
  obtain ⟨F,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := P) (target := P)
    (fun s hs => (pick s hs).elim fun t ht => ⟨t,(sat s t).mpr ht.2⟩)
    (fun _ _ _ _ hs ht => ((sat ..).mp hs).unique_l hZF.1 ((sat ..).mp ht))
    (by
      intro s t hs st
      obtain ⟨u,hu,su⟩ := pick s hs
      exact su.unique_l hZF.1 ((sat s t).mp st) ▸ hu)
  have edges s t : Entry_d M s t F ↔ M.mem s P ∧ Fc_swap_d i a b s t :=
    (graph s t).trans (and_congr_right fun _ => sat s t)
  have typed {m s t} (fs : Fp_at_d I ω A m s) (st : Entry_d M s t F) : Fp_at_d I ω A m t := by
    obtain ⟨u,fu,su⟩ := fc_swap_exists_l hZF fa alphabet pa pb fs
    exact su.unique_l hZF.1 ((edges s t).mp st).2 ▸ fu
  have inverse {s t} (st : Entry_d M s t F) : Fc_swap_d i a b t s := by
    obtain ⟨m,_,fs⟩ := (product.conditions s).mp (fn.input_mem_of_pairMember st)
    exact ((edges s t).mp st).2.inverse_l hZF fa alphabet pa pb fs
  have inv {s t} (st : Entry_d M s t F) : Entry_d M t s F :=
    (edges t s).mpr ⟨fn.output_mem_of_pairMember st,inverse st⟩
  have aut : Aut_d M P R P F := by
    refine aut_of_bij_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ⟨⟨fn,?_⟩,?_⟩ ?_ ?_
    · intro s t u su tu
      exact (inverse su).unique_l hZF.1 (inverse tu)
    · intro t ht
      obtain ⟨s,hs,ts⟩ := pick t ht
      exact ⟨s,hs,inv ((edges t s).mpr ⟨ht,ts⟩)⟩
    · intro s u t v st uv
      obtain ⟨m,_,fs⟩ := (product.conditions s).mp (fn.input_mem_of_pairMember st)
      have ft := typed fs st
      rw [product.order s u,product.order t v]
      exact ⟨fun h => ⟨fn.output_mem_of_pairMember st,fn.output_mem_of_pairMember uv,
        ((edges s t).mp st).2.le_l hZF fs ft ((edges u v).mp uv).2 h.2.2⟩,
        fun h => ⟨fn.input_mem_of_pairMember st,fn.input_mem_of_pairMember uv,
          (inverse st).le_l hZF ft fs (inverse uv) h.2.2⟩⟩
    · intro s t st
      exact iff_of_false (fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) P (eq ▸ fn.input_mem_of_pairMember st))
        (fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) P (eq ▸ fn.output_mem_of_pairMember st))
  have full : Fp_aut_d I P R F := ⟨aut,fun n s t st => by
    obtain ⟨m,_,fs⟩ := (product.conditions s).mp (fn.input_mem_of_pairMember st)
    have ft := typed fs st
    exact ⟨fun dom => fs.domain.eq hZF.1 dom ▸ ft.domain,fun dom => ft.domain.eq hZF.1 dom ▸ fs.domain⟩⟩
  refine ⟨F,full,edges,fun _ _ => inv,fun n outside => ⟨full,?_⟩⟩
  intro s t st k hk y
  have ne : k ≠ i := fun eq => outside (eq ▸ hk)
  have swap := ((edges s t).mp st).2
  constructor
  · intro ky
    exact (swap.2 k y).mpr ⟨y,ky,Or.inr ⟨ne,rfl⟩⟩
  · intro ky
    obtain ⟨z,kz,zy⟩ := (swap.2 k y).mp ky
    exact zy.elim (fun h => (ne h.1).elim) (fun h => h.2.symm ▸ kz)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 同时作用于有限尾部的逐行交换

只在两条给定条件共有且位于冻结前缀之外的坐标交换字母。各行互不干扰，
可用一次模型内替代装配有限乘积作用，长度仍是模型自己的内部有限长度。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def Ft_active_d (n p q i a b : M.Domain) : Prop := ¬ M.mem i n ∧ Entry_d M i a p ∧ Entry_d M i b q
def Ft_row_d (n p q i s t : M.Domain) : Prop :=
  (∃ a b, Ft_active_d n p q i a b ∧ Fs_swap_d a b s t) ∨ ((¬ ∃ a b, Ft_active_d n p q i a b) ∧ t = s)
def Ft_swap_d (n p q s t : M.Domain) : Prop :=
  (∀ v, M.mem v t → ∃ i y, KPair_d M v i y) ∧
    ∀ i y, Entry_d M i y t ↔ ∃ x, Entry_d M i x s ∧ Ft_row_d n p q i x y

def ft_active_m {d} (n p q i a b : Term d) : Formula 1 d := set[d] ⟪
  ⌜i⌝ₛ ∉ ⌜n⌝ₛ ∧ ⌜entry_m⌝ₚ(⌜i⌝ₛ,⌜a⌝ₛ,⌜p⌝ₛ) ∧ ⌜entry_m⌝ₚ(⌜i⌝ₛ,⌜b⌝ₛ,⌜q⌝ₛ)⟫
derive_free_closed ft_active_m
def ft_row_m {d} (n p q i s t : Term d) : Formula 1 d := set[d] ⟪
  (∃ a b, ⌜ft_active_m⌝ₚ(⌜n⌝ₛ,⌜p⌝ₛ,⌜q⌝ₛ,⌜i⌝ₛ,a,b) ∧ ⌜fs_swap_m⌝ₚ(a,b,⌜s⌝ₛ,⌜t⌝ₛ)) ∨
    ((¬ (∃ a b, ⌜ft_active_m⌝ₚ(⌜n⌝ₛ,⌜p⌝ₛ,⌜q⌝ₛ,⌜i⌝ₛ,a,b))) ∧ ⌜t⌝ₛ = ⌜s⌝ₛ)⟫
derive_free_closed ft_row_m
def ft_swap_m {d} (n p q s t : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isRelation kpair_convention_l⌝ₚ(⌜t⌝ₛ) ∧
    (∀ i y, ⌜entry_m⌝ₚ(i,y,⌜t⌝ₛ) ↔ ∃ x, ⌜entry_m⌝ₚ(i,x,⌜s⌝ₛ) ∧ ⌜ft_row_m⌝ₚ(⌜n⌝ₛ,⌜p⌝ₛ,⌜q⌝ₛ,i,x,y))⟫
derive_free_closed ft_swap_m

theorem ft_active_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n p q i a b : Term d) :
    Formula.satisfies ρ (ft_active_m n p q i a b) ↔ Ft_active_d (n.eval ρ) (p.eval ρ) (q.eval ρ) (i.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [ft_active_m,Ft_active_d,Formula.satisfies_conj_iff,Formula.satisfies_neg_iff,Formula.satisfies_mem_iff,entry_sat_l M hE]
theorem ft_row_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n p q i s t : Term d) :
    Formula.satisfies ρ (ft_row_m n p q i s t) ↔ Ft_row_d (n.eval ρ) (p.eval ρ) (q.eval ρ) (i.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [ft_row_m,Ft_row_d,Formula.satisfies_disj_iff,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff,ft_active_sat_l hE,fs_swap_sat_l hE,Formula.satisfies_extensionalEq_iff_eq hE,Definitional.Term.eval_weaken]
  rfl
theorem ft_swap_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n p q s t : Term d) :
    Formula.satisfies ρ (ft_swap_m n p q s t) ↔ Ft_swap_d (n.eval ρ) (p.eval ρ) (q.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [ft_swap_m,Ft_swap_d,Formula.isRelation,kpair_convention_l,Formula.satisfies_conj_iff,
    Formula.satisfies_forallMem_iff,Formula.satisfies_exists_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    kpair_sat_l M hE,entry_sat_l M hE,ft_row_sat_l hE,Definitional.Term.eval_weaken]
  rfl

section Row
variable (hE : Extensional M) {n p q i : M.Domain}
  (fp : ∀ i a b, Entry_d M i a p → Entry_d M i b p → a = b)
  (fq : ∀ i a b, Entry_d M i a q → Entry_d M i b q → a = b)
include hE fp fq

theorem Ft_row_d.unique_l {s t u : M.Domain} (h : Ft_row_d n p q i s t) (k : Ft_row_d n p q i s u) : t = u := by
  rcases h with ⟨a,b,active,swap⟩ | ⟨no,eq⟩ <;> rcases k with ⟨c,d,active',swap'⟩ | ⟨no',eq'⟩
  · have ec := fp i c a active'.2.1 active.2.1
    have ed := fq i d b active'.2.2 active.2.2
    subst c d
    exact swap.unique_l hE swap'
  · exact (no' ⟨a,b,active⟩).elim
  · exact (no ⟨c,d,active'⟩).elim
  · exact eq.trans eq'.symm

theorem Ft_row_d.mono_l {s t u v : M.Domain} (h : Ft_row_d n p q i s t) (k : Ft_row_d n p q i u v)
    (sub : M.MemberSubset s u) : M.MemberSubset t v := by
  rcases h with ⟨a,b,active,swap⟩ | ⟨no,eq⟩ <;> rcases k with ⟨c,d,active',swap'⟩ | ⟨no',eq'⟩
  · have ec := fp i c a active'.2.1 active.2.1
    have ed := fq i d b active'.2.2 active.2.2
    subst c d
    exact swap.mono_l swap' sub hE
  · exact (no' ⟨a,b,active⟩).elim
  · exact (no ⟨c,d,active'⟩).elim
  · exact eq.symm ▸ eq'.symm ▸ sub
end Row

variable (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
variable {ω A n p q l k : M.Domain} (hw : M.IsOmega ω)
  (fa : M.IsSetFunction (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) A)
  (fp : Fp_at_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω A l p)
  (fq : Fp_at_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω A k q)
include hw fa fp fq

private theorem ft_parameters_l {i a b κ : M.Domain} (active : Ft_active_d n p q i a b) (iκ : Entry_d M i κ A) :
    Pfn_d I ω κ a ∧ Pfn_d I ω κ b := by
  have read {p m a} (f : Fp_at_d I ω A m p) (ia : Entry_d M i a p) : Pfn_d I ω κ a := by
    obtain ⟨δ,j,iδ,hj,fn⟩ := f.coordinates i a ia
    have eq := fa.2 i δ κ iδ iκ
    subst δ
    exact ⟨fn.1,fun v x vx => ⟨hw.transitive (ZF.modelsKP hZF) j hj v (fn.input_mem_of_pairMember vx),fn.output_mem_of_pairMember vx⟩⟩
  exact ⟨read fp active.2.1,read fq active.2.2⟩

theorem ft_row_exists_l {i κ m s : M.Domain} (iκ : Entry_d M i κ A) (fs : M.IsSetFunctionFromTo I s m κ) :
    ∃ t, M.IsSetFunctionFromTo I t m κ ∧ Ft_row_d n p q i s t := by
  rcases Classical.em (∃ a b, Ft_active_d n p q i a b) with ⟨a,b,active⟩ | no
  · have params := ft_parameters_l hZF hw fa fp fq active iκ
    obtain ⟨t,ft,st⟩ := fs_swap_exists_l hZF params.1 params.2 fs
    exact ⟨t,ft,Or.inl ⟨a,b,active,st⟩⟩
  · exact ⟨s,fs,Or.inr ⟨no,rfl⟩⟩

theorem Ft_row_d.inverse_l {i κ m s t : M.Domain} (iκ : Entry_d M i κ A)
    (fs : M.IsSetFunctionFromTo I s m κ) (h : Ft_row_d n p q i s t) : Ft_row_d n p q i t s := by
  rcases h with ⟨a,b,active,swap⟩ | ⟨no,eq⟩
  · have params := ft_parameters_l hZF hw fa fp fq active iκ
    exact Or.inl ⟨a,b,active,swap.inverse_l hZF params.1 params.2 fs⟩
  · exact Or.inr ⟨no,eq.symm⟩

theorem ft_swap_exists_l {m s : M.Domain} (fs : Fp_at_d I ω A m s) : ∃ t, Fp_at_d I ω A m t ∧ Ft_swap_d n p q s t := by
  let ρ : Env M 4 := ⟨fun j => [n,p,q,s].get j,fun _ => n⟩
  let φ : BinarySchema 4 := { body := .existsE (.conj (entry_m (.bound 2) .newest (.bound 6))
    (ft_row_m (.bound 3) (.bound 4) (.bound 5) (.bound 2) .newest (.bound 1))) }
  have sat i y : φ.denote ρ i y ↔ ∃ x, Entry_d M i x s ∧ Ft_row_d n p q i x y := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,entry_sat_l M hZF.1,ft_row_sat_l hZF.1]
    rfl
  have total i (hi : M.mem i m) : ∃ y, φ.denote ρ i y := by
    obtain ⟨x,ix⟩ := (fs.domain i).mp hi
    obtain ⟨κ,j,iκ,_,fx⟩ := fs.coordinates i x ix
    obtain ⟨y,_,xy⟩ := ft_row_exists_l hZF hw fa fp fq iκ fx (n := n)
    exact ⟨y,(sat i y).mpr ⟨x,ix,xy⟩⟩
  have unique i x y (hx : φ.denote ρ i x) (hy : φ.denote ρ i y) : x = y := by
    obtain ⟨a,ia,ax⟩ := (sat i x).mp hx
    obtain ⟨b,ib,by₀⟩ := (sat i y).mp hy
    exact ax.unique_l hZF.1 fp.function.2 fq.function.2 (fs.function.2 i b a ib ia ▸ by₀)
  obtain ⟨W,range⟩ := ZF.exists_functionalImage hZF φ ρ m total unique
  obtain ⟨t,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total
    (fun i _ => unique i) (fun i y hi hy => (range y).mpr ⟨i,hi,hy⟩)
  have entries i y : Entry_d M i y t ↔ ∃ x, Entry_d M i x s ∧ Ft_row_d n p q i x y :=
    (graph i y).trans ((and_congr_right fun _ => sat i y).trans
      ⟨And.right,fun h => ⟨h.elim fun x hx => (fs.domain i).mpr ⟨x,hx.1⟩,h⟩⟩)
  refine ⟨t,⟨fn.1,fn.2.1,?_⟩,fn.1.1,entries⟩
  intro i y iy
  obtain ⟨x,ix,xy⟩ := (entries i y).mp iy
  obtain ⟨κ,j,iκ,hj,fx⟩ := fs.coordinates i x ix
  obtain ⟨z,fz,xz⟩ := ft_row_exists_l hZF hw fa fp fq iκ fx (n := n)
  exact ⟨κ,j,iκ,hj,xz.unique_l hZF.1 fp.function.2 fq.function.2 xy ▸ fz⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原两条乘积条件产生使尾部相容的实际自同构

并行逐行交换是有限个不交坐标作用的乘积。整个图保持长度、平方为恒等，
冻结前缀逐条不动；旧前缀一致时，交换后的两条条件有实际共同加强。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Ft_swap_d.unique_l (hE : Extensional M) {n p q s t u : M.Domain} (h : Ft_swap_d n p q s t) (k : Ft_swap_d n p q s u) : t = u :=
  entry_ext_l M hE h.1 k.1 (fun i y => (h.2 i y).trans (k.2 i y).symm)

private theorem ft_inverse_l {ω A n p q l k m s t : M.Domain} (hw : M.IsOmega ω) (fa : M.IsSetFunction I A)
    (fp : Fp_at_d I ω A l p) (fq : Fp_at_d I ω A k q) (fs : Fp_at_d I ω A m s) (ft : Fp_at_d I ω A m t)
    (h : Ft_swap_d n p q s t) : Ft_swap_d n p q t s := by
  have reverse {i x y} (ix : Entry_d M i x s) (xy : Ft_row_d n p q i x y) : Ft_row_d n p q i y x := by
    obtain ⟨κ,j,iκ,_,fx⟩ := fs.coordinates i x ix
    exact xy.inverse_l hZF hw fa fp fq iκ fx
  refine ⟨fs.function.1,fun i x => ⟨?_,?_⟩⟩
  · intro ix
    obtain ⟨y,iy⟩ := (ft.domain i).mp ((fs.domain i).mpr ⟨x,ix⟩)
    obtain ⟨x',ix',xy⟩ := (h.2 i y).mp iy
    have eq := fs.function.2 i x' x ix' ix
    subst x'
    exact ⟨y,iy,reverse ix xy⟩
  · rintro ⟨y,iy,yx⟩
    obtain ⟨z,iz,zy⟩ := (h.2 i y).mp iy
    exact (reverse iz zy).unique_l hZF.1 fp.function.2 fq.function.2 yx ▸ iz

private theorem ft_le_l {ω A n p q m s t u v : M.Domain}
    (pf : M.IsSetFunction I p) (qf : M.IsSetFunction I q) (fs : Fp_at_d I ω A m s) (ft : Fp_at_d I ω A m t)
    (st : Ft_swap_d n p q s t) (uv : Ft_swap_d n p q u v) (le : Fp_le_d I s u) : Fp_le_d I t v := by
  intro i y iy
  obtain ⟨x,ix,xy⟩ := (uv.2 i y).mp iy
  obtain ⟨z,iz,xz⟩ := le i x ix
  obtain ⟨w,iw⟩ := (ft.domain i).mp ((fs.domain i).mpr ⟨z,iz⟩)
  obtain ⟨z',iz',zw⟩ := (st.2 i w).mp iw
  have eq := fs.function.2 i z' z iz' iz
  subst z'
  exact ⟨w,iw,xy.mono_l hZF.1 pf.2 qf.2 zw xz⟩

theorem fp_tail_swap_l {ω A P R p q n : M.Domain} (hw : M.IsOmega ω) (fa : M.IsSetFunction I A)
    (product : Fp_product_d hZF ω A P R) (hp : M.mem p P) (hq : M.mem q P) :
    ∃ F, Fp_tail_d I n P R F ∧
      (∀ s t, Entry_d M s t F ↔ M.mem s P ∧ Ft_swap_d n p q s t) ∧
      (∀ s t, Entry_d M s t F → Entry_d M t s F) ∧
      ∃ l, M.mem l ω ∧ ∀ s t, Entry_d M s t F → ∀ i, ¬ M.mem i l →
        ∀ x, Entry_d M i x s ↔ Entry_d M i x t := by
  obtain ⟨l,hl,fp⟩ := (product.conditions p).mp hp
  obtain ⟨k,_,fq⟩ := (product.conditions q).mp hq
  let ρ : Env M 3 := ⟨fun i => [n,p,q].get i,fun _ => n⟩
  let φ : BinarySchema 3 := { body := ft_swap_m (.bound 2) (.bound 3) (.bound 4) (.bound 1) .newest }
  have sat s t : φ.denote ρ s t ↔ Ft_swap_d n p q s t := ft_swap_sat_l hZF.1 ..
  have pick s (hs : M.mem s P) : ∃ t, M.mem t P ∧ Ft_swap_d n p q s t := by
    obtain ⟨m,hm,fs⟩ := (product.conditions s).mp hs
    obtain ⟨t,ft,st⟩ := ft_swap_exists_l hZF hw fa fp fq fs (n := n)
    exact ⟨t,(product.conditions t).mpr ⟨m,hm,ft⟩,st⟩
  obtain ⟨F,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := P) (target := P)
    (fun s hs => (pick s hs).elim fun t ht => ⟨t,(sat s t).mpr ht.2⟩)
    (fun _ _ _ _ hs ht => ((sat ..).mp hs).unique_l hZF.1 ((sat ..).mp ht))
    (by
      intro s t hs st
      obtain ⟨u,hu,su⟩ := pick s hs
      exact su.unique_l hZF.1 ((sat s t).mp st) ▸ hu)
  have edges s t : Entry_d M s t F ↔ M.mem s P ∧ Ft_swap_d n p q s t :=
    (graph s t).trans (and_congr_right fun _ => sat s t)
  have typed {m s t} (fs : Fp_at_d I ω A m s) (st : Entry_d M s t F) : Fp_at_d I ω A m t := by
    obtain ⟨u,fu,su⟩ := ft_swap_exists_l hZF hw fa fp fq fs (n := n)
    exact su.unique_l hZF.1 ((edges s t).mp st).2 ▸ fu
  have inverse {s t} (st : Entry_d M s t F) : Ft_swap_d n p q t s := by
    obtain ⟨m,_,fs⟩ := (product.conditions s).mp (fn.input_mem_of_pairMember st)
    exact ft_inverse_l hZF hw fa fp fq fs (typed fs st) ((edges s t).mp st).2
  have inv {s t} (st : Entry_d M s t F) : Entry_d M t s F := (edges t s).mpr ⟨fn.output_mem_of_pairMember st,inverse st⟩
  have aut : Aut_d M P R P F := by
    refine aut_of_bij_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ⟨⟨fn,?_⟩,?_⟩ ?_ ?_
    · intro s t u su tu
      exact (inverse su).unique_l hZF.1 (inverse tu)
    · intro t ht
      obtain ⟨s,hs,ts⟩ := pick t ht
      exact ⟨s,hs,inv ((edges t s).mpr ⟨ht,ts⟩)⟩
    · intro s u t v st uv
      obtain ⟨m,_,fs⟩ := (product.conditions s).mp (fn.input_mem_of_pairMember st)
      have ft := typed fs st
      rw [product.order s u,product.order t v]
      exact ⟨fun h => ⟨fn.output_mem_of_pairMember st,fn.output_mem_of_pairMember uv,
        ft_le_l hZF fp.function fq.function fs ft ((edges s t).mp st).2 ((edges u v).mp uv).2 h.2.2⟩,
        fun h => ⟨fn.input_mem_of_pairMember st,fn.input_mem_of_pairMember uv,
          ft_le_l hZF fp.function fq.function ft fs (inverse st) (inverse uv) h.2.2⟩⟩
    · intro s t st
      exact iff_of_false (fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) P (eq ▸ fn.input_mem_of_pairMember st))
        (fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) P (eq ▸ fn.output_mem_of_pairMember st))
  have full : Fp_aut_d I P R F := ⟨aut,fun m s t st => by
    obtain ⟨j,_,fs⟩ := (product.conditions s).mp (fn.input_mem_of_pairMember st)
    have ft := typed fs st
    exact ⟨fun dom => fs.domain.eq hZF.1 dom ▸ ft.domain,fun dom => ft.domain.eq hZF.1 dom ▸ fs.domain⟩⟩
  have fixed {s t} (st : Entry_d M s t F) (i : M.Domain) (no : ¬ ∃ a b, Ft_active_d n p q i a b) :
      ∀ x, Entry_d M i x s ↔ Entry_d M i x t := by
    have swap := ((edges s t).mp st).2
    intro x
    exact ⟨fun ix => (swap.2 i x).mpr ⟨x,ix,Or.inr ⟨no,rfl⟩⟩,fun ix => by
      obtain ⟨y,iy,yx⟩ := (swap.2 i x).mp ix
      exact yx.elim (fun ⟨a,b,h,_⟩ => (no ⟨a,b,h⟩).elim) (fun h => h.2.symm ▸ iy)⟩
  refine ⟨F,⟨full,fun s t st i hi => fixed st i (fun ⟨_,_,h⟩ => h.1 hi)⟩,edges,
    (fun _ _ => inv),l,hl,?_⟩
  intro s t st i outside
  exact fixed st i (fun ⟨a,_,active⟩ => outside ((fp.domain i).mpr ⟨a,active.2.1⟩))

/-- 唯一前提是被冻结坐标已相容；任意尾条件均可由原交换图变为相容。 -/
theorem fp_tail_homogeneous_l {ω A P R n p q : M.Domain} (hw : M.IsOmega ω) (fa : M.IsSetFunction I A)
    (product : Fp_product_d hZF ω A P R) (hp : M.mem p P) (hq : M.mem q P) (agree : Fp_agree_d hZF n p q) :
    ∃ F s, Fp_tail_d I n P R F ∧ Entry_d M p s F ∧ Cmp_d M P R P s q := by
  obtain ⟨F,tail,edges,_⟩ := fp_tail_swap_l hZF hw fa product hp hq (n := n)
  obtain ⟨s,ps⟩ := tail.1.aut.total p hp
  have hs := (tail.1.aut.domain p s ps).2
  obtain ⟨l,_,fp⟩ := (product.conditions p).mp hp
  obtain ⟨k,_,fq⟩ := (product.conditions q).mp hq
  refine ⟨F,s,tail,ps,product.compatible_l hZF hw hs hq ?_⟩
  intro i a b ia ib j x y jx jy
  obtain ⟨a₀,ia₀,row⟩ := (((edges p s).mp ps).2.2 i a).mp ia
  rcases row with ⟨a',b',active,swap⟩ | ⟨no,eq⟩
  · have ea := fp.function.2 i a' a₀ active.2.1 ia₀
    have eb := fq.function.2 i b' b active.2.2 ib
    subst a' b'
    obtain ⟨_,_,_,_,fa₀⟩ := fp.coordinates i a₀ ia₀
    obtain ⟨_,_,_,_,fb⟩ := fq.coordinates i b ib
    obtain ⟨z,jz,zx⟩ := (swap.2 j x).mp jx
    exact Fs_val_d.unique_l fa₀.1.2 fb.1.2 zx (Or.inl ⟨z,y,jz,jy,Or.inl ⟨rfl,rfl⟩⟩)
  · have hi : M.mem i n := Classical.byContradiction (fun outside => no ⟨a₀,b,outside,ia₀,ib⟩)
    exact agree i hi a₀ b ia₀ ib j x y (eq ▸ jx) jy

end YesMetaZFC.Model.Forcing.Internal

/-! ## 尾部作用固定规范实数并名字及全部旧前缀名字参数

固定旧坐标即固定旧前缀的每个条件，名字复合律随后给出逐名字固定。
规范实数并名字与旧前缀参数可共同进入原公式的力迫不变性。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Fp_tail_d.prefix_names_l {ω A P R F n C S b : M.Domain}
    (product : Fp_product_d hZF ω A P R) (stage : Fp_stage_d hZF ω A n C S b)
    (hn : M.mem n ω) (tail : Fp_tail_d I n P R F) :
    ∀ s, Name_d M C s → Nmap_d M F s s := by
  have section₀ := stage.stage.product_read_l hZF product hn
  have point p (hp : M.mem p C) : Entry_d M p p F := by
    obtain ⟨q,pq⟩ := tail.1.aut.total p ((section₀.1 p).mp hp).1
    have hq := (section₀.1 q).mpr ⟨(tail.1.aut.domain p q pq).2,
      (tail.1.lengths n p q pq).mp ((section₀.1 p).mp hp).2⟩
    have fp := (stage.stage.conditions p).mp hp
    have fq := (stage.stage.conditions q).mp hq
    have eq : p = q := fp.function.1.eq_of_pairMember_iff hZF.1 fq.function.1 (fun i s =>
      ⟨fun is => (tail.2 p q pq i ((fp.domain i).mpr ⟨s,is⟩) s).mp is,
        fun is => (tail.2 p q pq i ((fq.domain i).mpr ⟨s,is⟩) s).mpr is⟩)
    exact eq.symm ▸ pq
  obtain ⟨G,_,_,entries,restrict⟩ := tail.1.restrict_l hZF product stage hn
  have identity p q : Entry_d M p q G ↔ M.mem p C ∧ q = p := (entries p q).trans
    ⟨fun ⟨hp,pq⟩ => ⟨hp,tail.1.aut.functional p q p pq (point p hp)⟩,
      fun ⟨hp,eq⟩ => ⟨hp,eq.symm ▸ point p hp⟩⟩
  exact fun s ns => (restrict s s ns).mpr (nmap_identity_l hZF identity ns)

theorem Rp_name_d.tail_eq_l {ω A P R r F n s p : M.Domain} (name : Rp_name_d hZF ω A P r)
    (product : Fp_product_d hZF ω A P R) (tail : Fp_tail_d I n P R F)
    (image : Nmap_d M F r s) (hp : M.mem p P) : Eq_force_d M P R P p s r := by
  have eq := nmap_unique_l M hZF.1 (check_ind_l M hZF) F r s r image (name.aut_fixed_l hZF product tail.1)
  exact eq.symm ▸ eq_force_refl_l (product.order_l hZF) hZF hp name.name

theorem Rp_name_d.tail_forces_l {ω A P R r F n C S b : M.Domain} (name : Rp_name_d hZF ω A P r)
    (product : Fp_product_d hZF ω A P R) (stage : Fp_stage_d hZF ω A n C S b)
    (hn : M.mem n ω) (tail : Fp_tail_d I n P R F)
    {a k} (φ : Formula a k) (closed : φ.FreeClosed) (ρ : Env M k)
    (params : ∀ i, ρ.bound i = r ∨ Name_d M C (ρ.bound i)) {p q} (pq : Entry_d M p q F) :
    Forces_d M P R P φ ρ p ↔ Forces_d M P R P φ ρ q := by
  have sub : M.MemberSubset C P := fun p hp => ((stage.stage.product_read_l hZF product hn).1 p).mp hp |>.1
  exact aut_forces_closed_l hZF tail.1.aut φ closed ρ ρ
    (fun i => (params i).elim (fun eq => eq.symm ▸ name.name) (name_conditions_mono_l sub))
    (fun i => (params i).elim (fun eq => eq.symm ▸ name.aut_fixed_l hZF product tail.1)
      (tail.prefix_names_l hZF product stage hn (ρ.bound i))) pq

theorem Fp_tail_d.comp_l {n P R F G : M.Domain} (h : Fp_tail_d I n P R F) (k : Fp_tail_d I n P R G) :
    ∃ H, Fp_tail_d I n P R H ∧ ∀ p q, Entry_d M p q H ↔ ∃ s, Entry_d M p s F ∧ Entry_d M s q G := by
  obtain ⟨H,aut,edges⟩ := aut_comp_l hZF h.1.aut k.1.aut
  refine ⟨H,⟨⟨aut,?_⟩,?_⟩,edges⟩
  · intro m p q pq
    obtain ⟨s,ps,sq⟩ := (edges p q).mp pq
    exact (h.1.lengths m p s ps).trans (k.1.lengths m s q sq)
  · intro p q pq i hi s
    obtain ⟨t,pt,tq⟩ := (edges p q).mp pq
    exact (h.2 p t pt i hi s).trans (k.2 t q tq i hi s)

/-- 任意实际尾坐标交换自动给出同一规范名字的固定证书。 -/
theorem Rp_name_d.coordinate_swap_l {ω A P R r i κ a b n : M.Domain} (name : Rp_name_d hZF ω A P r)
    (product : Fp_product_d hZF ω A P R) (fa : M.IsSetFunction I A) (alphabet : Entry_d M i κ A)
    (pa : Pfn_d I ω κ a) (pb : Pfn_d I ω κ b) (outside : ¬ M.mem i n) :
    ∃ F, Fp_tail_d I n P R F ∧ Nmap_d M F r r ∧
      ∀ s t, Entry_d M s t F ↔ M.mem s P ∧ Fc_swap_d i a b s t := by
  obtain ⟨F,aut,edges,_,tails⟩ := fp_coordinate_swap_l hZF fa alphabet pa pb product
  exact ⟨F,tails n outside,name.aut_fixed_l hZF product aut,edges⟩

/-- 从两条原乘积条件的实际尾坐标自动恢复交换参数，无需另给局部力迫实例。 -/
theorem Rp_name_d.swap_l {ω A P R r i p q a b n : M.Domain} (name : Rp_name_d hZF ω A P r)
    (product : Fp_product_d hZF ω A P R) (hw : M.IsOmega ω) (fa : M.IsSetFunction I A)
    (hp : M.mem p P) (hq : M.mem q P) (ip : Entry_d M i a p) (iq : Entry_d M i b q)
    (outside : ¬ M.mem i n) : ∃ F, Fp_tail_d I n P R F ∧ Nmap_d M F r r ∧
      ∀ s t, Entry_d M s t F ↔ M.mem s P ∧ Fc_swap_d i a b s t := by
  obtain ⟨m,_,fp⟩ := (product.conditions p).mp hp
  obtain ⟨k,_,fq⟩ := (product.conditions q).mp hq
  obtain ⟨κ,l,iκ,hl,ga⟩ := fp.coordinates i a ip
  obtain ⟨δ,j,iδ,hj,gb⟩ := fq.coordinates i b iq
  have eq := fa.2 i δ κ iδ iκ
  subst δ
  have pa : Pfn_d I ω κ a := ⟨ga.1,fun v x vx =>
    ⟨hw.transitive (ZF.modelsKP hZF) l hl v (ga.input_mem_of_pairMember vx),ga.output_mem_of_pairMember vx⟩⟩
  have pb : Pfn_d I ω κ b := ⟨gb.1,fun v x vx =>
    ⟨hw.transitive (ZF.modelsKP hZF) j hj v (gb.input_mem_of_pairMember vx),gb.output_mem_of_pairMember vx⟩⟩
  exact name.coordinate_swap_l hZF product fa iκ pa pb outside

end YesMetaZFC.Model.Forcing.Internal

/-! ## 尾部弱齐性消去力迫条件的尾坐标

正文允许规范实数并名字及全部旧前缀名字参数。一个条件迫使正文，当且仅当
其旧前缀已迫使正文；在实际泛型中，真值遂由同一有限前缀滤子全局决定。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Rp_name_d.tail_reduce_l {ω A P R r n C S b p a : M.Domain} (name : Rp_name_d hZF ω A P r)
    (hw : M.IsOmega ω) (fa : M.IsSetFunction I A) (product : Fp_product_d hZF ω A P R)
    (stage : Fp_stage_d hZF ω A n C S b) (hn : M.mem n ω)
    {u k} (φ : Formula u k) (closed : φ.FreeClosed) (ρ : Env M k)
    (params : ∀ i, ρ.bound i = r ∨ Name_d M C (ρ.bound i))
    (hp : M.mem p P) (ha : M.mem a C) (cut : M.IsRestrictionOf I a p n) :
    Forces_d M P R P φ ρ p ↔ Forces_d M P R P φ ρ a := by
  have O := product.order_l hZF
  have sub : M.MemberSubset C P := fun q hq => ((stage.stage.product_read_l hZF product hn).1 q).mp hq |>.1
  have names i : Name_d M P (ρ.bound i) := (params i).elim (fun eq => eq.symm ▸ name.name) (name_conditions_mono_l sub)
  have regular := forces_closed_regular_l O hZF φ closed ρ names
  have nz {q} (hq : M.mem q P) : q ≠ P := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) P (eq ▸ hq)
  have pa : Entry_d M p a R := (product.order p a).mpr ⟨hp,sub a ha,fun i s is =>
    ⟨s,((cut.2 i s).mp is).2,fun _ h => h⟩⟩
  constructor
  · intro forced
    apply regular.2 a (sub a ha) (nz (sub a ha))
    intro q qa
    have agree : Fp_agree_d hZF n p q := by
      intro i hi s t is it j x y jx jy
      obtain ⟨v,iv,sv⟩ := ((product.order q a).mp qa.2.2).2.2 i s ((cut.2 i s).mpr ⟨hi,is⟩)
      obtain ⟨m,_,fq⟩ := (product.conditions q).mp qa.1
      have eq := fq.function.2 i v t iv it
      obtain ⟨_,_,_,_,ft⟩ := fq.coordinates i t it
      obtain ⟨c,pair,hc⟩ := jx
      exact ft.1.2 j x y ⟨c,pair,eq ▸ sv c hc⟩ jy
    obtain ⟨F,s,tail,ps,v,vs,vq⟩ := fp_tail_homogeneous_l hZF hw fa product hp qa.1 agree
    have transported := (name.tail_forces_l hZF product stage hn tail φ closed ρ params ps).mp forced
    exact ⟨v,⟨vs.1,vs.2.1,vq⟩,regular.1 s v (tail.1.aut.domain p s ps).2 vs transported⟩
  · exact regular.1 a p (sub a ha) ⟨hp,nz hp,pa⟩

/-- 真值的证据总可取自已固定的前缀滤子，尾部泛型不再参与判定。 -/
theorem Rp_name_d.prefix_truth_l {ω A P R r n C S b W : M.Domain} (name : Rp_name_d hZF ω A P r)
    (hw : M.IsOmega ω) (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    (stage : Fp_stage_d hZF ω A n C S b) (hn : M.mem n ω)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    {k} (φ : Formula 1 k) (closed : φ.FreeClosed) (ρ : Env M k)
    (params : ∀ i, ρ.bound i = r ∨ Name_d M C (ρ.bound i))
    (η : Env (extension_l M hZF P R P G) k) (values : ∀ i, Qval_d M P R P G (ρ.bound i) (η.bound i)) :
    Formula.satisfies η φ ↔ ∃ a, M.mem a C ∧ G a ∧ Forces_d M P R P φ ρ a := by
  have O := product.order_l hZF
  have truth := forcing_closed_truth_l hZF O generic φ closed ρ η values
  refine ⟨fun h => ?_,fun ⟨a,_,ha,forced⟩ => truth.mp ⟨a,ha,forced⟩⟩
  obtain ⟨p,hp,forced⟩ := truth.mpr h
  have small := product.project_generic_l hZF hw hn fa stage.stage generic
  obtain ⟨a,ha,q,hq,qa⟩ := small.inhabited
  obtain ⟨u,hu,up,uq⟩ := generic.directed p q hp hq
  obtain ⟨m,hm,fu⟩ := (product.conditions u).mp (generic.proper u hu).1
  have ua := ((product.order u q).mp uq).2.2.trans_l I qa
  obtain ⟨c,cut,fc⟩ := fu.restrict_l hZF (ua.domain_l I fu ((stage.stage.conditions a).mp ha))
  have hc := (stage.stage.conditions c).mpr fc
  have hcp := (product.conditions c).mpr ⟨n,hn,fc⟩
  have uc : Entry_d M u c R := (product.order u c).mpr ⟨(generic.proper u hu).1,hcp,fun i s is =>
    ⟨s,((cut.2 i s).mp is).2,fun _ h => h⟩⟩
  have cg := generic.upward u c hu hcp uc
  have sub : M.MemberSubset C P := fun z hz => ((stage.stage.product_read_l hZF product hn).1 z).mp hz |>.1
  have regular := forces_closed_regular_l O hZF φ closed ρ
    (fun i => (params i).elim (fun eq => eq.symm ▸ name.name) (name_conditions_mono_l sub))
  have forceu := regular.1 p u (generic.proper p hp).1 ⟨(generic.proper u hu).1,(generic.proper u hu).2,up⟩ forced
  exact ⟨c,hc,cg,(name.tail_reduce_l hZF hw fa.1 product stage hn φ closed ρ params (generic.proper u hu).1 hc cut).mp forceu⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 规范实数并参数下的顶条件全局判定

地参数使用同一空条件的检查名字，规范实数并名字使用已经证明的实际不变性。
弱齐性把任一条件的力迫提升到顶条件，并与任意实际泛型扩张真值精确对应。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Fp_product_d.whom_l {ω A P R : M.Domain} (product : Fp_product_d hZF ω A P R)
    (hw : M.IsOmega ω) (fa : M.IsSetFunction I A) : Whom_d M P R P := by
  obtain ⟨o,empty⟩ := KP.exists_empty (ZF.modelsKP hZF)
  intro p q hp _ hq _
  obtain ⟨F,s,tail,ps,cmp⟩ := fp_tail_homogeneous_l hZF hw fa product hp hq
    (show Fp_agree_d hZF o p q from fun i hi => (empty i hi).elim)
  exact ⟨F,s,tail.1.aut,ps,cmp⟩

theorem Fp_product_d.empty_top_l {ω A P R o : M.Domain} (product : Fp_product_d hZF ω A P R)
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x o) : M.mem o P ∧ ∀ p, M.mem p P → Entry_d M p o R := by
  obtain ⟨z,hz,hzω⟩ := hw.1.1
  have eq : z = o := hZF.1.eq_of_same_members z o (fun x => iff_of_false (hz x) (empty x))
  have seq := Structure.IsSequenceOfLength.empty I empty
  have ho := (product.conditions o).mpr ⟨o,eq ▸ hzω,seq.2.1,seq.2.2,fun _ _ ⟨v,_,hv⟩ => (empty v hv).elim⟩
  exact ⟨ho,fun p hp => (product.order p o).mpr ⟨hp,ho,fun _ _ ⟨v,_,hv⟩ => (empty v hv).elim⟩⟩

theorem Fp_aut_d.empty_fixed_l {ω A P R o F : M.Domain} (product : Fp_product_d hZF ω A P R)
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x o) (aut : Fp_aut_d I P R F) : Entry_d M o o F := by
  obtain ⟨q,oq⟩ := aut.aut.total o (product.empty_top_l hZF hw empty).1
  have dom := (aut.lengths o o q oq).mp (Structure.IsSequenceOfLength.empty I empty).2.2
  obtain ⟨_,_,fq⟩ := (product.conditions q).mp (aut.aut.domain o q oq).2
  have eq : q = o := hZF.1.eq_of_same_members q o (fun v => iff_of_false (by
    intro hv
    obtain ⟨i,s,pair⟩ := fq.function.1 v hv
    exact empty i ((dom i).mpr ⟨s,⟨v,pair,hv⟩⟩)) (empty v))
  exact eq ▸ oq

/-- 允许规范实数并名字与任意有限地参数；不把实数并名字冒充检查名字。 -/
theorem Rp_name_d.top_force_l {ω A P R r o : M.Domain} (name : Rp_name_d hZF ω A P r)
    (hw : M.IsOmega ω) (fa : M.IsSetFunction I A) (product : Fp_product_d hZF ω A P R)
    (empty : ∀ x, ¬ M.mem x o) {a k} (φ : Formula a k) (closed : φ.FreeClosed) (ρ : Env M k)
    (params : ∀ i, ρ.bound i = r ∨ ∃ x, Check_d M o x (ρ.bound i)) :
    ∀ p, M.mem p P → (Forces_d M P R P φ ρ p ↔ Forces_d M P R P φ ρ o) := by
  have O := product.order_l hZF
  obtain ⟨ho,top⟩ := product.empty_top_l hZF hw empty
  have names i : Name_d M P (ρ.bound i) := (params i).elim (fun eq => eq.symm ▸ name.name)
    (fun ⟨x,check⟩ => check_name_l M (check_range_l M hZF) ho check)
  have regular := forces_closed_regular_l O hZF φ closed ρ names
  have nz {p} (hp : M.mem p P) : p ≠ P := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) P (eq ▸ hp)
  intro p hp
  constructor
  · intro forced
    apply regular.2 o ho (nz ho)
    intro q hq
    have agree : Fp_agree_d hZF o p q := fun i hi => (empty i hi).elim
    obtain ⟨F,s,tail,ps,v,vs,vq⟩ := fp_tail_homogeneous_l hZF hw fa product hp hq.1 agree
    have fixed := tail.1.empty_fixed_l hZF product hw empty
    have parameters i : Nmap_d M F (ρ.bound i) (ρ.bound i) := (params i).elim
      (fun eq => eq.symm ▸ name.aut_fixed_l hZF product tail.1)
      (fun ⟨x,check⟩ => aut_check_fixed_l hZF tail.1.aut fixed check)
    have transported := (aut_forces_closed_l hZF tail.1.aut φ closed ρ ρ names parameters ps).mp forced
    exact ⟨v,⟨vs.1,vs.2.1,vq⟩,regular.1 s v (tail.1.aut.domain p s ps).2 vs transported⟩
  · exact regular.1 o p ho ⟨hp,nz hp,top p hp⟩

theorem Rp_name_d.top_decides_l {ω A P R r o : M.Domain} (name : Rp_name_d hZF ω A P r)
    (hw : M.IsOmega ω) (fa : M.IsSetFunction I A) (product : Fp_product_d hZF ω A P R)
    (empty : ∀ x, ¬ M.mem x o) {a k} (φ : Formula a k) (closed : φ.FreeClosed) (ρ : Env M k)
    (params : ∀ i, ρ.bound i = r ∨ ∃ x, Check_d M o x (ρ.bound i)) :
    Forces_d M P R P φ ρ o ∨ Forces_d M P R P (.neg φ) ρ o := by
  rcases Classical.em (Forces_d M P R P φ ρ o) with yes | no
  · exact Or.inl yes
  · exact Or.inr ((forces_neg_l hZF.1 φ ρ o).mpr (fun p hp forced =>
      no ((name.top_force_l hZF hw fa product empty φ closed ρ params p hp.1).mp forced)))

theorem Rp_name_d.top_truth_l {ω A P R r o : M.Domain} (name : Rp_name_d hZF ω A P r)
    (hw : M.IsOmega ω) (fa : M.IsSetFunction I A) (product : Fp_product_d hZF ω A P R)
    (empty : ∀ x, ¬ M.mem x o) {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    {k} (φ : Formula 1 k) (closed : φ.FreeClosed) (ρ : Env M k)
    (params : ∀ i, ρ.bound i = r ∨ ∃ x, Check_d M o x (ρ.bound i))
    (η : Env (extension_l M hZF P R P G) k) (values : ∀ i, Qval_d M P R P G (ρ.bound i) (η.bound i)) :
    Forces_d M P R P φ ρ o ↔ Formula.satisfies η φ := by
  have truth := forcing_closed_truth_l hZF (product.order_l hZF) generic φ closed ρ η values
  constructor
  · intro forced
    obtain ⟨p,hp⟩ := generic.inhabited
    exact truth.mp ⟨p,hp,(name.top_force_l hZF hw fa product empty φ closed ρ params p (generic.proper p hp).1).mpr forced⟩
  · intro valid
    obtain ⟨p,hp,forced⟩ := truth.mpr valid
    exact (name.top_force_l hZF hw fa product empty φ closed ρ params p (generic.proper p hp).1).mp forced

end YesMetaZFC.Model.Forcing.Internal
