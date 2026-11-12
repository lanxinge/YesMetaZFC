import YesMetaZFC.Model.Forcing.Ground.ProductProjection
import YesMetaZFC.Model.Forcing.Ground.RealCodeImage
import YesMetaZFC.Model.SetTheory.Internal.Quotient
import YesMetaZFC.Model.Forcing.Extension.Isomorphism
import YesMetaZFC.SetTheory.Collapse.RelationIso
import YesMetaZFC.Model.Forcing.Ground.Collapse

/-! # 泛型名字商的实际背景集合编码

名字域由原模型中的名字公式分离，等价关系与隶属关系由同一泛型接受的
原子力迫分离。等价类及其全体由原有集合商构造产生，不选择名字代表。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hM : M.Models ZF) {c X R : M.Domain}
  (source : Smem_d (kp_pair_l (ZF.modelsKP hM)) c X R) (trans : M.TransitiveSet X)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1).Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "N" => smdl_structure_l I (R := R) (And.left (And.right (And.left source)))

private def bg_atom_m (k : Bool) : Formula 1 6 :=
  if k then eq_force_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)
  else mem_force_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)

private theorem bg_atom_closed_l (k : Bool) : (bg_atom_m k).FreeClosed := by
  cases k <;> simp -implicitDefEqProofs [bg_atom_m]

/-- 商类图同时读取 Lean 名字商的等号与隶属；所有编码对象都在背景模型中。 -/
structure Bg_quot_d (B T z : (N).Domain) (H A q C S : M.Domain) : Prop where
  inside : M.MemberSubset A X
  names : ∀ t : (N).Domain, M.mem t.val A ↔ Name_d N B t
  function : Fn0_d A C q
  onto : ∀ a, M.mem a C → ∃ t, Rd_entry_d t a q
  typed : ∀ a b, Rd_entry_d a b S → M.mem a C ∧ M.mem b C
  kernel : ∀ s t x y a b, Qval_d N B T z (fun p => M.mem p.val H) s x →
    Qval_d N B T z (fun p => M.mem p.val H) t y → Rd_entry_d s.val a q → Rd_entry_d t.val b q →
      (a = b ↔ x = y)
  member : ∀ s t x y a b, Qval_d N B T z (fun p => M.mem p.val H) s x →
    Qval_d N B T z (fun p => M.mem p.val H) t y → Rd_entry_d s.val a q → Rd_entry_d t.val b q →
      (Rd_entry_d a b S ↔ (extension_l N native B T z (fun p => M.mem p.val H)).mem x y)

include trans in
theorem bg_quotient_l {B T z : (N).Domain} {H : M.Domain}
    (O : Cond_order_d N B T z) (generic : Gset_d B.val T.val z.val X H) :
    ∃ A q C S, Bg_quot_d hM source native B T z H A q C S := by
  let G : (N).Domain → Prop := fun p => M.mem p.val H
  have g := ((source.generic_code_l I hM.1 trans (ZF.modelsKP native) B T z H).mp generic).2
  let nm : Formula 1 2 := name_m (.bound 0) (.bound 1)
  have nc : nm.FreeClosed := by simp -implicitDefEqProofs [nm]
  let η : Env M 2 := ⟨fun i => [X,B.val].get i,fun _ => X⟩
  let ν : UnarySchema 2 := {
    body := lr_rel_m nm (.bound 1) (fun i => .bound (([2,0] : List (Fin 3)).get i))
    freeClosed := lr_rel_closed_l nm nc _ _ rfl (fun _ => rfl) }
  have nameSat (t : (N).Domain) : ν.denote η t.val ↔ Name_d N B t :=
    (lr_rel_decode_l I source.1 source.2 trans nm nc
      (⟨fun i => [B,t].get i,fun _ => t⟩ : Env N 2) (η.push t.val) (.bound 1)
      (fun i => .bound (([2,0] : List (Fin 3)).get i)) rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))).trans
      (name_sat_l N native.1 _ _ _)
  obtain ⟨A,sep⟩ := ZF.separation_exists_d hM ν η X
  have inside : M.MemberSubset A X := fun t ht => ((sep t).mp ht).1
  have names (t : (N).Domain) : M.mem t.val A ↔ Name_d N B t :=
    (sep t.val).trans ((and_iff_right t.property).trans (nameSat t))
  -- 两种原子共用一个背景接受公式，泛型仍是原集合 H。
  let ρ : Env M 5 := ⟨fun i => [X,B.val,T.val,z.val,H].get i,fun _ => X⟩
  let φ (k : Bool) : BinarySchema 5 := {
    body := Formula.existsMem (.bound 2) (.conj (.mem .newest (.bound 7))
      (lr_rel_m (bg_atom_m k) (.bound 3) (fun i => .bound (([4,5,6,0,2,1] : List (Fin 8)).get i))))
    freeClosed := ⟨⟨rfl,rfl⟩,⟨⟨rfl,rfl⟩,lr_rel_closed_l _ (bg_atom_closed_l k) _ _ rfl (fun _ => rfl)⟩⟩ }
  have hit (k : Bool) (s t : (N).Domain) : (φ k).denote ρ s.val t.val ↔
      ∃ p, G p ∧ (if k then Eq_force_d N B T z p s t else Mem_force_d N B T z p s t) := by
    have decode (p : (N).Domain) := lr_rel_decode_l I source.1 source.2 trans (bg_atom_m k) (bg_atom_closed_l k)
      (⟨fun i => [B,T,z,p,s,t].get i,fun _ => t⟩ : Env N 6) (((ρ.push s.val).push t.val).push p.val) (.bound 3)
      (fun i => .bound (([4,5,6,0,2,1] : List (Fin 8)).get i)) rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))
    have atom (p : (N).Domain) : Formula.satisfies (⟨fun i => [B,T,z,p,s,t].get i,fun _ => t⟩ : Env N 6) (bg_atom_m k) ↔
        (if k then Eq_force_d N B T z p s t else Mem_force_d N B T z p s t) := by
      cases k <;> simp only [bg_atom_m,Bool.false_eq_true,if_false,if_true,eq_force_sat_l N native.1,mem_force_sat_l N native.1] <;> rfl
    change (∃ p, M.mem p X ∧ M.mem p H ∧ _) ↔ _
    exact ⟨fun ⟨p,hp,hH,h⟩ => ⟨⟨p,hp⟩,hH,(atom ⟨p,hp⟩).mp ((decode ⟨p,hp⟩).mp h)⟩,
      fun ⟨p,hp,h⟩ => ⟨p.val,p.property,hp,(decode p).mpr ((atom p).mpr h)⟩⟩
  obtain ⟨E,_,eqs⟩ := ZF.exists_setRelationOn_of_denote hM I (φ true) ρ A
  obtain ⟨V,_,mems⟩ := ZF.exists_setRelationOn_of_denote hM I (φ false) ρ A
  have eqRead (s t : (N).Domain) {x y} (sx : Qval_d N B T z G s x) (ty : Qval_d N B T z G t y) :
      Rd_entry_d s.val t.val E ↔ x = y :=
    (eqs s.val t.val).trans ((and_iff_right ((names s).mpr (qval_name_l sx))).trans
      ((and_iff_right ((names t).mpr (qval_name_l ty))).trans ((hit true s t).trans (qval_eq_l O native g sx ty))))
  have memRead (s t : (N).Domain) {x y} (sx : Qval_d N B T z G s x) (ty : Qval_d N B T z G t y) :
      Rd_entry_d s.val t.val V ↔ (extension_l N native B T z G).mem x y :=
    (mems s.val t.val).trans ((and_iff_right ((names s).mpr (qval_name_l sx))).trans
      ((and_iff_right ((names t).mpr (qval_name_l ty))).trans ((hit false s t).trans (qval_mem_forcing_l O native g sx ty))))
  have val (s : M.Domain) (hs : M.mem s A) : ∃ x, Qval_d N B T z G ⟨s,inside s hs⟩ x :=
    name_value_l ((names ⟨s,inside s hs⟩).mp hs)
  have equiv : Qt_equiv_d A E := by
    refine ⟨fun s hs => ?_,fun s t st => ?_,fun s t v st tv => ?_⟩
    · obtain ⟨x,sx⟩ := val s hs
      exact (eqRead _ _ sx sx).mpr rfl
    · have hs := ((eqs s t).mp st).1
      have ht := ((eqs s t).mp st).2.1
      obtain ⟨x,sx⟩ := val s hs
      obtain ⟨y,ty⟩ := val t ht
      exact (eqRead _ _ ty sx).mpr ((eqRead _ _ sx ty).mp st).symm
    · have hs := ((eqs s t).mp st).1
      have ht := ((eqs s t).mp st).2.1
      have hv := ((eqs t v).mp tv).2.1
      obtain ⟨x,sx⟩ := val s hs
      obtain ⟨y,ty⟩ := val t ht
      obtain ⟨w,vw⟩ := val v hv
      exact (eqRead _ _ sx vw).mpr (((eqRead _ _ sx ty).mp st).trans ((eqRead _ _ ty vw).mp tv))
  obtain ⟨q,C,quotient⟩ := qt_map_exists_l hM A E
  have kernel (s t : (N).Domain) {x y a b} (sx : Qval_d N B T z G s x) (ty : Qval_d N B T z G t y)
      (sa : Rd_entry_d s.val a q) (tb : Rd_entry_d t.val b q) : a = b ↔ x = y :=
    (quotient.kernel_l hM.1 equiv sa tb).trans (eqRead s t sx ty)
  let δ : Env M 2 := ⟨fun i => [q,V].get i,fun _ => A⟩
  let ψ : BinarySchema 2 := { body := set[4] ⟪∃ s t,
    ⌜rd_entry0_m⌝ₚ(s,⌜(.bound 1 : Term 4)⌝ₛ,⌜(.bound 2 : Term 4)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(t,⌜(.bound 0 : Term 4)⌝ₛ,⌜(.bound 2 : Term 4)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(s,t,⌜(.bound 3 : Term 4)⌝ₛ)⟫ }
  have sat a b : ψ.denote δ a b ↔ ∃ s t, Rd_entry_d s a q ∧ Rd_entry_d t b q ∧ Rd_entry_d s t V := by
    simp only [ψ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,rd_entry0_sat_l hM.1]
    rfl
  obtain ⟨S,_,edges⟩ := ZF.exists_setRelationOn_of_denote hM I ψ δ C
  refine ⟨A,q,C,S,inside,names,quotient.function,fun a ha => (quotient.range a).mp ha,
    fun a b ab => ⟨((edges a b).mp ab).1,((edges a b).mp ab).2.1⟩,
    fun s t x y a b => kernel s t,?_⟩
  intro s t x y a b sx ty sa tb
  constructor
  · intro ab
    obtain ⟨u,v,ua,vb,uv⟩ := (sat a b).mp ((edges a b).mp ab).2.2
    obtain ⟨w,uw⟩ := val u (quotient.function.bound_l ua).1
    obtain ⟨z',vz⟩ := val v (quotient.function.bound_l vb).1
    have ex : w = x := (kernel _ _ uw sx ua sa).mp rfl
    have ey : z' = y := (kernel _ _ vz ty vb tb).mp rfl
    exact ex ▸ ey ▸ (memRead _ _ uw vz).mp uv
  · intro xy
    exact (edges a b).mpr ⟨(quotient.function.bound_l sa).2,(quotient.function.bound_l tb).2,
      (sat a b).mpr ⟨s.val,t.val,sa,tb,(memRead s t sx ty).mpr xy⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原名字商在背景模型中的传递呈示

商中非空集合的名字原像有条目极小元；原子真值把商前驱回拉为该名字的
实际子名字。内部良基性与外延性因此成立，原 Mostowski 定理产生完整呈示。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hM : M.Models ZF) {c X R : M.Domain}
  (source : Smem_d (kp_pair_l (ZF.modelsKP hM)) c X R) (trans : M.TransitiveSet X)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1).Models ZF)
variable {B T z : ((smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1)).Domain} {H A q C S : M.Domain}
include trans

theorem bg_quot_wf_l (order : Cond_order_d (smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1) B T z)
    (generic : Gset_d B.val T.val z.val X H) (code : Bg_quot_d hM source native B T z H A q C S) : Wf_rel_d (M := M) C S := by
  let N := smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1
  let G : N.Domain → Prop := fun p => M.mem p.val H
  rcases code with ⟨inside,names,fn,onto,_,kernel,member⟩
  have g := ((source.generic_code_l (kp_pair_l (ZF.modelsKP hM)) hM.1 trans (ZF.modelsKP native) B T z H).mp generic).2
  have ni : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have nf := smem_full_l (kp_pair_l (ZF.modelsKP hM)) source trans
  intro D sub ⟨a,ha⟩
  let ρ : Env M 2 := ⟨fun i => [D,q].get i,fun _ => D⟩
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 1) (rd_entry0_m (.bound 1) .newest (.bound 3)) }
  have sat t : φ.denote ρ t ↔ ∃ b, M.mem b D ∧ Rd_entry_d t b q := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_existsMem_iff,rd_entry0_sat_l hM.1]; rfl
  obtain ⟨U,sep⟩ := ZF.separation_exists_d hM φ ρ A
  have pre t : M.mem t U ↔ M.mem t A ∧ ∃ b, M.mem b D ∧ Rd_entry_d t b q :=
    (sep t).trans (and_congr_right fun _ => sat t)
  obtain ⟨t,ta⟩ := onto a (sub a ha)
  obtain ⟨t,ht,minimal⟩ := entry_min_l hM ⟨t,(pre t).mpr ⟨(fn.bound_l ta).1,a,ha,ta⟩⟩
  obtain ⟨htA,a,ha,ta⟩ := (pre t).mp ht
  let t₀ : N.Domain := ⟨t,inside t htA⟩
  obtain ⟨x,tx⟩ := name_value_l (M := N) (B := B) (R := T) (z := z) (U := G) (t := t₀) ((names t₀).mp htA)
  refine ⟨a,ha,fun b hb ba => ?_⟩
  obtain ⟨s,sb⟩ := onto b (sub b hb)
  let s₀ : N.Domain := ⟨s,inside s (fn.bound_l sb).1⟩
  obtain ⟨y,sy⟩ := name_value_l (M := N) (B := B) (R := T) (z := z) (U := G) (t := s₀) ((names s₀).mp (fn.bound_l sb).1)
  have yx := Iff.mp (member s₀ t₀ y x b a sy tx sb ta) ba
  obtain ⟨u,p,up,_,uy⟩ := (@qval_mem_l N B T z G order native g t₀ x y tx).mp yx
  have hu := (names u).mpr (qval_name_l uy)
  obtain ⟨d,_,ud⟩ := fn.2.1 u.val hu
  have eq : d = b := (kernel u s₀ y y d b uy sy ud sb).mpr rfl
  exact minimal u.val p.val ((image_entry_iff_l (M := N) (N := M) Subtype.val ni nf
    (KP.exists_pair (ZF.modelsKP native)) hM.1 u p t₀).mp up)
    ((pre u.val).mpr ⟨hu,b,hb,eq ▸ ud⟩)

theorem bg_quot_ext_l (order : Cond_order_d (smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1) B T z)
    (generic : Gset_d B.val T.val z.val X H) (code : Bg_quot_d hM source native B T z H A q C S) : Wc_ext_d (M := M) C S := by
  let N := smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1
  let G : N.Domain → Prop := fun p => M.mem p.val H
  rcases code with ⟨inside,names,fn,onto,_,kernel,member⟩
  have g := ((source.generic_code_l (kp_pair_l (ZF.modelsKP hM)) hM.1 trans (ZF.modelsKP native) B T z H).mp generic).2
  intro a ha b hb same
  obtain ⟨s,sa⟩ := onto a ha
  obtain ⟨t,tb⟩ := onto b hb
  let s₀ : N.Domain := ⟨s,inside s (fn.bound_l sa).1⟩
  let t₀ : N.Domain := ⟨t,inside t (fn.bound_l tb).1⟩
  obtain ⟨x,sx⟩ := name_value_l (M := N) (B := B) (R := T) (z := z) (U := G) (t := s₀) ((names s₀).mp (fn.bound_l sa).1)
  obtain ⟨y,ty⟩ := name_value_l (M := N) (B := B) (R := T) (z := z) (U := G) (t := t₀) ((names t₀).mp (fn.bound_l tb).1)
  apply (kernel s₀ t₀ x y a b sx ty sa tb).mpr
  apply (extension_ext_l order native g).eq_of_same_members
  intro w
  obtain ⟨u,nu,uw⟩ := value_name_l w
  obtain ⟨d,hd,ud⟩ := fn.2.1 u.val ((names u).mpr nu)
  exact (member u s₀ w x d a uw sx ud sa).symm.trans
    ((same d hd).trans (member u t₀ w y d b uw ty ud tb))

/-- 坍塌图保留每个原名字的商类；实际嵌入覆盖其像对象的全部背景成员。 -/
theorem bg_quot_collapse_l (order : Cond_order_d (smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1) B T z)
    (generic : Gset_d B.val T.val z.val X H) (code : Bg_quot_d hM source native B T z H A q C S) :
    let N := smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1
    let G : N.Domain → Prop := fun p => M.mem p.val H
    let E := extension_l N native B T z G
    ∃ Y F, M.TransitiveSet Y ∧ Wc_graph_d (M := M) C S F ∧ M.IsSetBijectionFromTo (kp_pair_l (ZF.modelsKP hM)) F C Y ∧
      ∃ e : E.Domain → M.Domain, Function.Injective e ∧
        (∀ x, M.mem (e x) Y) ∧ (∀ x y, M.mem y (e x) ↔ ∃ w, E.mem w x ∧ e w = y) ∧
        ∀ t x a, Qval_d N B T z G t x → Rd_entry_d t.val a q → Rd_entry_d a (e x) F := by
  let N := smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1
  let G : N.Domain → Prop := fun p => M.mem p.val H
  let E := extension_l N native B T z G
  obtain ⟨Y,F,transY,graph,bij,rel⟩ := wc_iso_l hM
    (bg_quot_wf_l hM source trans native order generic code) (bg_quot_ext_l hM source trans native order generic code)
  rcases code with ⟨inside,names,fn,onto,_,kernel,member⟩
  have hall (x : E.Domain) : ∃ y, ∃ t a, Qval_d N B T z G t x ∧ Rd_entry_d t.val a q ∧ Rd_entry_d a y F := by
    obtain ⟨t,nt,tx⟩ := value_name_l x
    obtain ⟨a,ha,ta⟩ := fn.2.1 t.val ((names t).mpr nt)
    obtain ⟨y,_,ay⟩ := bij.1.1.2.2 a ha
    exact ⟨y,t,a,tx,ta,ay⟩
  obtain ⟨e,values⟩ := Classical.axiomOfChoice hall
  have keep t x a (tx : Qval_d N B T z G t x) (ta : Rd_entry_d t.val a q) : Rd_entry_d a (e x) F := by
    obtain ⟨s,b,sx,sb,be⟩ := values x
    exact (kernel s t x x b a sx tx sb ta).mpr rfl ▸ be
  have inj : Function.Injective e := by
    intro x y eq
    obtain ⟨s,a,sx,sa,ax⟩ := values x
    obtain ⟨t,b,ty,tb,by'⟩ := values y
    exact (kernel s t x y a b sx ty sa tb).mp (bij.1.2 a b (e y) (eq ▸ ax) by')
  have range x : M.mem (e x) Y := by
    obtain ⟨t,a,tx,ta,ax⟩ := values x
    exact bij.1.1.output_mem_of_pairMember ax
  refine ⟨Y,F,transY,graph,bij,e,inj,range,?_,keep⟩
  intro x y
  obtain ⟨t,a,tx,ta,ax⟩ := values x
  constructor
  · intro hy
    obtain ⟨b,hb,ba,by'⟩ := ((graph.2 a (e x) ax).2.2 y).mp hy
    obtain ⟨s,sb⟩ := onto b hb
    let s₀ : N.Domain := ⟨s,inside s (fn.bound_l sb).1⟩
    obtain ⟨w,sw⟩ := name_value_l (M := N) (B := B) (R := T) (z := z) (U := G) (t := s₀) ((names s₀).mp (fn.bound_l sb).1)
    exact ⟨w,(member s₀ t w x b a sw tx sb ta).mp ba,bij.1.1.1.2 b (e w) y (keep s₀ w b sw sb) by'⟩
  · rintro ⟨w,wx,rfl⟩
    obtain ⟨s,b,sw,sb,bw⟩ := values w
    exact (rel b a (e w) (e x) bw ax).mp ((member s t w x b a sw tx sb ta).mpr wx)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 背景传递呈示逐点还原地模型

把检查名字经原商类及坍塌的复合编码为背景中的实际函数图。
对该图的原公式作内部成员归纳，证明复合为恒等；无需外部良基归纳。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hM : M.Models ZF) {c X R : M.Domain}
  (source : Smem_d (kp_pair_l (ZF.modelsKP hM)) c X R) (trans : M.TransitiveSet X)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1).Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
include trans

theorem bg_extension_l {B T z : (smdl_structure_l I (R := R) source.1.2.1).Domain} {H : M.Domain}
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) B T z)
    (generic : Gset_d B.val T.val z.val X H) :
    let N := smdl_structure_l I (R := R) source.1.2.1
    let G : N.Domain → Prop := fun p => M.mem p.val H
    let E := extension_l N native B T z G
    ∃ Y : M.Domain, ∃ e : E.Domain → M.Domain, M.TransitiveSet Y ∧ (∀ x, M.mem (e x) Y) ∧
      Function.Injective e ∧ (∀ x y, M.mem y (e x) ↔ ∃ w, E.mem w x ∧ e w = y) ∧
      ∀ a x, Gval_d N B T z G a x → e x = a.val := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let G : N.Domain → Prop := fun p => M.mem p.val H
  let E := extension_l N native B T z G
  have g := ((source.generic_code_l I hM.1 trans (ZF.modelsKP native) B T z H).mp generic).2
  obtain ⟨A,q,C,S,code⟩ := bg_quotient_l hM source trans native O generic
  obtain ⟨Y,F,ht,_,bij,e,ei,range,ef,keep⟩ := bg_quot_collapse_l hM source trans native O generic code
  obtain ⟨b,hb⟩ := g.inhabited
  obtain ⟨j,checks,jf,_⟩ := check_map_l O native g hb
  have ground a := (gval_check_map_l O native g hb j checks a (j a)).mpr rfl
  let cm : Formula 1 3 := check_m (.bound 0) (.bound 1) (.bound 2)
  have cc : cm.FreeClosed := by simp -implicitDefEqProofs [cm]
  let ρ : Env M 4 := ⟨fun i => [X,b.val,q,F].get i,fun _ => X⟩
  let φ : BinarySchema 4 := {
    body := Formula.existsMem (.bound 2) (.conj
      (lr_rel_m cm (.bound 3) (fun i => .bound (([4,2,0] : List (Fin 7)).get i)))
      (.existsE (.conj (rd_entry0_m (.bound 1) .newest (.bound 6)) (rd_entry0_m .newest (.bound 2) (.bound 7)))))
    freeClosed := ⟨⟨rfl,rfl⟩,⟨lr_rel_closed_l cm cc _ _ rfl (fun _ => rfl),by
      simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]⟩⟩ }
  have sat (a : N.Domain) (y : M.Domain) : φ.denote ρ a.val y ↔
      ∃ τ : N.Domain, Check_d N b a τ ∧ ∃ d, Rd_entry_d τ.val d q ∧ Rd_entry_d d y F := by
    have decode (τ : N.Domain) := (lr_rel_decode_l I source.1 source.2 trans cm cc
      (⟨fun i => [b,a,τ].get i,fun _ => a⟩ : Env N 3) (((ρ.push a.val).push y).push τ.val) (.bound 3)
      (fun i => .bound (([4,2,0] : List (Fin 7)).get i)) rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))).trans
        (check_sat_l N native.1 _ _ _ _)
    simp only [φ,BinarySchema.denote,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_exists_iff,rd_entry0_sat_l hM.1]
    exact ⟨fun ⟨τ,hτ,check,d,td,dy⟩ => ⟨⟨τ,hτ⟩,(decode ⟨τ,hτ⟩).mp check,d,td,dy⟩,
      fun ⟨τ,check,d,td,dy⟩ => ⟨τ.val,τ.property,(decode τ).mpr check,d,td,dy⟩⟩
  have graphValue (a : N.Domain) {y : M.Domain} (h : φ.denote ρ a.val y) : y = e (j a) := by
    obtain ⟨τ,check,d,td,dy⟩ := (sat a y).mp h
    exact bij.1.1.1.2 d y (e (j a)) dy (keep τ (j a) d (checks a τ check) td)
  have total (a : N.Domain) : φ.denote ρ a.val (e (j a)) := by
    obtain ⟨τ,check,name,_⟩ := zf_check_l N native (g.proper b hb).1 a
    obtain ⟨d,_,td⟩ := code.function.2.1 τ.val ((code.names τ).mpr name)
    exact (sat a _).mpr ⟨τ,check,d,td,keep τ (j a) d (checks a τ check) td⟩
  obtain ⟨f,fn,edges⟩ := ZF.exists_setFunctionFromTo_of_denote hM I φ ρ (source := X) (target := Y)
    (fun a ha => ⟨e (j ⟨a,ha⟩),total ⟨a,ha⟩⟩)
    (fun a ha y w hy hw => (graphValue ⟨a,ha⟩ hy).trans (graphValue ⟨a,ha⟩ hw).symm)
    (fun a ha hx h => (graphValue ⟨a,hx⟩ h).symm ▸ range (j ⟨a,hx⟩))
  have graph (a : N.Domain) (y : M.Domain) : Rd_entry_d a.val y f ↔ y = e (j a) :=
    (edges a.val y).trans ((and_iff_right a.property).trans
      ⟨graphValue a,fun eq => eq.symm ▸ total a⟩)
  have full {a y : M.Domain} (ay : Rd_entry_d a y f) (w : M.Domain) :
      M.mem w y ↔ ∃ d, M.mem d a ∧ Rd_entry_d d w f := by
    let a₀ : N.Domain := ⟨a,fn.input_mem_of_pairMember ay⟩
    have eq := (graph a₀ y).mp ay
    rw [eq,ef (j a₀) w]
    constructor
    · rintro ⟨v,hv,ev⟩
      obtain ⟨d,da,jd⟩ := (jf a₀ v).mp hv
      exact ⟨d.val,((source.2 d.val a).mp da).2.2,(graph d w).mpr (ev.symm.trans (congrArg e jd).symm)⟩
    · rintro ⟨d,da,dw⟩
      let d₀ : N.Domain := ⟨d,trans a a₀.property d da⟩
      exact ⟨j d₀,(jf a₀ (j d₀)).mpr ⟨d₀,(source.2 d a).mpr ⟨d₀.property,a₀.property,da⟩,rfl⟩,
        ((graph d₀ w).mp dw).symm⟩
  -- 归纳只读取实际集合图 f；源和目标都仍是同一个背景模型。
  let δ : Env M 1 := ⟨fun _ => f,fun _ => f⟩
  let ψ : UnarySchema 1 := { body := .forallE (.imp (rd_entry0_m (.bound 1) .newest (.bound 2))
    (Formula.extensionalEq .newest (.bound 1))) }
  have ps a : ψ.denote δ a ↔ ∀ y, Rd_entry_d a y f → y = a := by
    simp only [ψ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      rd_entry0_sat_l hM.1,Formula.satisfies_extensionalEq_iff_eq hM.1]; rfl
  have fixed := check_ind_l M hM ψ δ (fun a ih => (ps a).mpr (by
    intro y ay
    apply hM.1.eq_of_same_members
    intro w
    rw [full ay w]
    constructor
    · rintro ⟨d,da,dw⟩
      exact ((ps d).mp (ih d da) w dw).symm ▸ da
    · intro wa
      obtain ⟨v,_,wv⟩ := fn.2.2 w (trans a (fn.input_mem_of_pairMember ay) w wa)
      exact ⟨w,wa,(ps w).mp (ih w wa) v wv ▸ wv⟩))
  have commute (a : N.Domain) : e (j a) = a.val := (ps a.val).mp (fixed a.val) _ ((graph a _).mpr rfl)
  refine ⟨Y,e,ht,range,ei,ef,fun a x value => ?_⟩
  exact congrArg e (value.unique_l O native g (ground a)) |>.trans (commute a)

end YesMetaZFC.Model.Forcing.Internal
