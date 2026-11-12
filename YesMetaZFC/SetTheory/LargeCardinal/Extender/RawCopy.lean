import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyMaps
import YesMetaZFC.Model.SetTheory.Relations.CrossMeasure
import YesMetaZFC.Model.SetTheory.Relations.LayerComposition
import YesMetaZFC.Model.SetTheory.ReducedPower.Copy
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationSuccessor
import YesMetaZFC.Model.SetTheory.ReducedPower.CopyConstant
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyClass

/-! # 两张原关系图之间的实际测度对应

父模型的规范化子集先由共同图回收到所属模型。两侧实际测度都是原
扩展器在对应支撑处的值；所属初等图保持成员关系，遂得到坐标迹的测度对应。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_copy_measure_l
    {ω c N T c' N' T' σ X R Y S π Γ Γ' k k' κ κ' z z' n m d d' y y'
      F F' b b' u u' D E i i' t t' U V A A' B B' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ) (ext : Rf_ext_d I N T)
    (agree : Er_agree_d I ω N T κ z Γ X R k)
    (agree' : Er_agree_d I ω N' T' κ' z' Γ' Y S k')
    (hn : M.mem n ω) (hnm : Rd_entry_d n m z) (space : Er_space_d I N T κ m d)
    (hd : Rd_entry_d d d' σ) (hdy : Rd_entry_d d y k) (hdy' : Rd_entry_d d' y' k')
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d T)
    (ec : ∀ x, M.mem x E ↔ M.mem x N' ∧ Rd_entry_d x d' T')
    (fi : M.IsSetFunctionFromTo I i D N) (fi' : M.IsSetFunctionFromTo I i' E N')
    (id : ∀ x v, Rd_entry_d x v i ↔ M.mem x D ∧ x = v)
    (id' : ∀ x v, Rd_entry_d x v i' ↔ M.mem x E ∧ x = v)
    (rt : M.IsRestrictionOf I t k D) (rt' : M.IsRestrictionOf I t' k' E)
    (hF : Rd_entry_d F F' σ) (hb : Rd_entry_d b b' σ)
    (value : Rf_val_d I N T b u F) (value' : Rf_val_d I N' T' b' u' F')
    (unique : ∀ x v w, Rf_val_d I N' T' x v F' → Rf_val_d I N' T' x w F' → v = w)
    (bounded : ∀ a, M.mem a N → Rd_entry_d a u T → ∀ x, M.mem x N → Rd_entry_d x a T → Rd_entry_d x d T)
    (bounded' : ∀ a, M.mem a N' → Rd_entry_d a u' T' → ∀ x, M.mem x N' → Rd_entry_d x a T' → Rd_entry_d x d' T')
    (measure : ∀ C, M.mem C U ↔ ∃ a, M.mem a N ∧ Rd_entry_d a u T ∧ Rt_trace_d I D i T a C)
    (measure' : ∀ C, M.mem C V ↔ ∃ a, M.mem a N' ∧ Rd_entry_d a u' T' ∧ Rt_trace_d I E i' T' a C)
    (maps : Er_maps_d I ω N T κ z k k' π σ)
    (hA : M.mem A X) (sub : ∀ x, M.mem x X → Rd_entry_d x A R → Rd_entry_d x y R)
    (hAA : Rd_entry_d A A' π) (trace : Rt_trace_d I D t R A B) (trace' : Rt_trace_d I E t' S A' B') :
    M.mem B U ↔ M.mem B' V := by
  obtain ⟨y₀, hdy₀, subsets⟩ := agree.subsets_l I hn hnm space
  have eq := agree.injection.1.1.2 d y₀ y hdy₀ hdy
  subst y₀
  obtain ⟨a, ha, ad, hak⟩ := (subsets A hA).mp sub
  obtain ⟨a', ha', haa⟩ := map.1.1.2.2 a ha
  have hak' := maps n m d a a' A A' hn hnm space ha ad hak haa hAA
  let d₀ : (smdl_structure_l I (R := T) mx.2.1).Domain := ⟨d, map.1.1.input_mem_of_pairMember hd⟩
  let d₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨d', map.1.1.output_mem_of_pairMember hd⟩
  let a₀ : (smdl_structure_l I (R := T) mx.2.1).Domain := ⟨a, ha⟩
  let a₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨a', ha'⟩
  let ρ : Env (smdl_structure_l I (R := T) mx.2.1) 2 := ⟨Fin.cases d₀ (fun _ => a₀), fun _ => d₀⟩
  let η : Env (smdl_structure_l I (R := T') my.2.1) 2 := ⟨Fin.cases d₁ (fun _ => a₁), fun _ => d₁⟩
  have moved := smap_source_l I hZF hω mx my map (Formula.subset (.bound 1) .newest)
    (by simp -implicitDefEqProofs) ρ η (Fin.cases hd (fun _ => haa))
  have ad' := (Formula.satisfies_subset_iff ..).mp
    (moved.mp ((Formula.satisfies_subset_iff ..).mpr (fun x => ad x.val x.property)))
  -- 实际坐标图覆盖有限幂，规范化子集的迹唯一确定原集合码。
  have ft := rt.isSetFunctionFromTo agree.injection.1 (fun x hx => agree.downward d x
    (agree.injection.1.input_mem_of_pairMember hdy) ((dc x).mp hx).1 ((dc x).mp hx).2)
  have ft' := rt'.isSetFunctionFromTo agree'.injection.1 (fun x hx => agree'.downward d' x
    (agree'.injection.1.input_mem_of_pairMember hdy') ((ec x).mp hx).1 ((ec x).mp hx).2)
  have left := rr_measure_read_l I mx.2.1 (ext.native_l I mx.2.1) d₀
    ⟨u, (value.bounds_l I).2.1⟩ a₀ dc fi id agree.injection agree.predecessors ft rt hak
    (fun x => ad x.val x.property) (fun a hu x => bounded a.val a.property hu x.val x.property) measure trace
  have ext' : Rf_ext_d I N' T' := map.extensional_l hZF hω mx my ext
  have right := rr_measure_read_l I my.2.1 (ext'.native_l I my.2.1) d₁
    ⟨u', (value'.bounds_l I).2.1⟩ a₁ ec fi' id' agree'.injection agree'.predecessors ft' rt' hak'
    ad' (fun a hu x => bounded' a.val a.property hu x.val x.property) measure' trace'
  exact left.trans ((ec_measure_image_l hZF hω mx my map hF hb haa value value' unique).trans right.symm)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 两端实际原关系分量之间的完整初等复制

支撑码、有限幂对象及父模型中的定义域像均由给定图推出。原测度的有界性
和取值唯一性直接读取同一个所属扩展器。子集一致性构造相对超滤，再由
实际统一化及完整 Łoś 构造复制；商关系、代表族和测度保持原对象。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_code_d.copy_l
    {ω c N T c' N' T' σ h X R h' Y S π Γ Γ' k k' z z' L L' a a' o o' n : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ)
    (hN : (smdl_structure_l I (R := T) mx.2.1).Models KP)
    (hN' : (smdl_structure_l I (R := T') my.2.1).Models KP)
    (w ξ ℓ f : (smdl_structure_l I (R := T) mx.2.1).Domain)
    (w' ξ' ℓ' f' : (smdl_structure_l I (R := T') my.2.1).Domain)
    (hξ : Rd_entry_d ξ.val ξ'.val σ)
    (hℓ : Rd_entry_d ℓ.val ℓ'.val σ) (hf : Rd_entry_d f.val f'.val σ)
    (numbers : Rr_layer_d I ω N T w.val z) (numbers' : Rr_layer_d I ω N' T' w'.val z')
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (length' : ∀ x, M.mem x L' ↔ M.mem x N' ∧ Rd_entry_d x ℓ'.val T')
    (loc : It_local_d I w.val N T ξ.val ℓ.val f.val)
    (powers : ∀ m d : (smdl_structure_l I (R := T) mx.2.1).Domain,
      (smdl_structure_l I (R := T) mx.2.1).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l I (R := T) mx.2.1).IsPowerSetOf p d)
    (parent : Smdl_d I h X R) (parent' : Smdl_d I h' Y S) (copy : Smap_d I ω h h' X Y π)
    (px : Rf_ext_d I X R) (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (agree : Er_agree_d I ω N T ξ.val z Γ X R k)
    (agree' : Er_agree_d I ω N' T' ξ'.val z' Γ' Y S k')
    (maps : Er_maps_d I ω N T ξ.val z k k' π σ)
    (small : ∀ n m d y, M.mem n ω → Rd_entry_d n m z → Er_space_d I N T ξ.val m d →
      Rd_entry_d d y k → Rf_small_d I X R y)
    (fa : Fn0_d n L a) (fa' : Fn0_d n L' a') (assign : Smap_assign_d I n σ a a')
    (code : Er_code_d I ω L N T ξ.val f.val z X R k a o)
    (code' : Er_code_d I ω L' N' T' ξ'.val f'.val z' Y S k' a' o') :
    ∃ D E t t' y y' U V G H p q C C' W W' K j j₀ j₁,
      Fn0_d D X t ∧ Fn0_d E Y t' ∧ Rd_entry_d y y' π ∧
      (∃ n m b d u i, Er_frame_d I ω L N T ξ.val f.val z X R k a o n m b d u D i t y U G p C W) ∧
      (∃ n m b d u i, Er_frame_d I ω L' N' T' ξ'.val f'.val z' Y S k' a' o' n m b d u E i t' y' V H q C' W') ∧
      M.IsSetFunctionFromTo I K G H ∧
      (∀ g v, Rd_entry_d g v K ↔ M.mem g G ∧ M.mem v H ∧ Rc_copy_d I X R y t Y S t' π g v) ∧
      Smap_d I ω o o' C C' j ∧ Rp_lift_d I K p q j ∧
      (∀ B A, Rd_entry_d B A j ↔ M.mem B C ∧ M.mem A C' ∧ Rc_class_d I X R y t Y S t' π B A) ∧
      (∀ B A, Rd_entry_d B A j ↔ Er_class_d I ω L N T ξ.val f.val z X R k
        L' N' T' ξ'.val f'.val z' Y S k' π σ a a' B A) ∧
      (∀ B A, Rd_entry_d B A j → ∀ g, M.mem g B → ∃ g', M.mem g' A ∧ Rc_copy_d I X R y t Y S t' π g g') ∧
      Smap_d I ω h o X C j₀ ∧ Smap_d I ω h' o' Y C' j₁ ∧
      (∀ x B, Rd_entry_d x B j₀ ↔ M.mem x X ∧ ∃ g, Fn0_d D X g ∧ M.mem g B ∧ Rs_const_d D x g ∧ Rd_entry_d g B p) ∧
      (∀ x B, Rd_entry_d x B j₁ ↔ M.mem x Y ∧ ∃ g, Fn0_d E Y g ∧ M.mem g B ∧ Rs_const_d E x g ∧ Rd_entry_d g B q) ∧
      (∀ x x' B A, Rd_entry_d x x' π → Rd_entry_d x B j₀ →
        (Rd_entry_d B A j ↔ Rd_entry_d x' A j₁)) ∧
      (∀ B A, Rd_entry_d t B p → Rd_entry_d t' A q → Rd_entry_d B A j) := by
  obtain ⟨n₀, m, b, d, u, D, i, t, y, U, G, p, C, W,
    hn, fa₀, hnm, fn, graph, space, value, dc, fi, id, rt, hdy, measure, family, quotient⟩ := code
  obtain ⟨n₁, m', b', d', u', E, i', t', y', V, H, q, C', W',
    _, fa₁, hnm', fn', graph', space', value', ec, fi', id', rt', hdy', measure', family', quotient'⟩ := code'
  have eq := fa₀.domain_eq_l hZF.1 fa
  subst n₀
  have eq := fa₁.domain_eq_l hZF.1 fa'
  subst n₁
  have ext : Rf_ext_d I N T := fun x hx y hy same => congrArg Subtype.val
    (hN.1.eq_of_same_members ⟨x, hx⟩ ⟨y, hy⟩ (fun z => same z.val z.property))
  have ext' : Rf_ext_d I N' T' := map.extensional_l hZF hω mx my ext
  have ex := ext.native_l I mx.2.1
  have ey := ext'.native_l I my.2.1
  obtain ⟨hw, digits⟩ := numbers.omega_map_l I hZF hω mx my map ext ext' numbers'
  have hmm := digits n m m' hnm hnm'
  have hbb := Rr_finite_d.map_l hZF hω mx my map ext numbers numbers' fa fa' assign
    ⟨n, m, hn, fa, hnm, fn, graph⟩ ⟨n, m', hn, fa', hnm', fn', graph'⟩
  let m₀ : (smdl_structure_l I (R := T) mx.2.1).Domain := ⟨m, numbers.injection.1.output_mem_of_pairMember hnm⟩
  let m₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨m', numbers'.injection.1.output_mem_of_pairMember hnm'⟩
  let b₀ : (smdl_structure_l I (R := T) mx.2.1).Domain := ⟨b, fn.mem_l I⟩
  let b₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨b', fn'.mem_l I⟩
  let d₀ : (smdl_structure_l I (R := T) mx.2.1).Domain := ⟨d, space.elim fun h _ => h 0⟩
  let d₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨d', space'.elim fun h _ => h 0⟩
  let u₀ : (smdl_structure_l I (R := T) mx.2.1).Domain := ⟨u, (value.bounds_l I).2.1⟩
  let u₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨u', (value'.bounds_l I).2.1⟩
  have ds := (er_space_native_l I mx.2.1 ex ξ m₀ d₀).mp space
  have es := (er_space_native_l I my.2.1 ey ξ' m₁ d₁).mp space'
  -- 有限幂的像由同一原公式确定，不额外指定目标定义域。
  have hdd := space.image_unique_l I hZF hω mx my map ey hξ hmm space'
  have fb := numbers.function_range_l hZF ex m₀ ℓ b₀ hnm fa
    (fun x hx => ((length x).mp hx).2) fn graph
  have fb' := numbers'.function_range_l hZF ey m₁ ℓ' b₁ hnm' fa'
    (fun x hx => ((length' x).mp hx).2) fn' graph'
  have next := loc.map_l hZF hω mx my map hw hξ hℓ hf
  -- 所属扩展器的同一测度族给出成员有界性和函数值唯一性。
  have actual := loc.read_l I mx.2.1 (kp_pair_l hN) ex w ξ ℓ f
  have actual' := next.read_l I my.2.1 (kp_pair_l hN') ey w' ξ' ℓ' f'
  have ultra := actual.measures.at_l ex ((rf_val_native_l I mx.2.1 ex b₀ u₀ f).mp value) fb ds
  have ultra' := actual'.measures.at_l ey ((rf_val_native_l I my.2.1 ey b₁ u₁ f').mp value') fb' es
  have bounded a (ha : M.mem a N) (hu : Rd_entry_d a u T) x (hx : M.mem x N) (hxa : Rd_entry_d x a T) :=
    ultra.1.1 ⟨a, ha⟩ hu ⟨x, hx⟩ hxa
  have bounded' a (ha : M.mem a N') (hu : Rd_entry_d a u' T') x (hx : M.mem x N') (hxa : Rd_entry_d x a T') :=
    ultra'.1.1 ⟨a, ha⟩ hu ⟨x, hx⟩ hxa
  have unique x v w (hv : Rf_val_d I N' T' x v f'.val) (hw : Rf_val_d I N' T' x w f'.val) : v = w :=
    congrArg Subtype.val (actual'.measures.function ⟨x, (hv.bounds_l I).1⟩
      ⟨v, (hv.bounds_l I).2.1⟩ ⟨w, (hw.bounds_l I).2.1⟩
      ((rf_val_native_l I my.2.1 ey _ _ f').mp hv) ((rf_val_native_l I my.2.1 ey _ _ f').mp hw))
  -- 对有限幂自身应用子集交换条件，确定父模型中的定义域像。
  obtain ⟨y₂, _, hyy₂⟩ := copy.1.1.2.2 y (agree.injection.1.output_mem_of_pairMember hdy)
  have hdy₂ := maps n m d d d' y y₂ hn hnm space d₀.property (fun _ _ h => h) hdy hdd hyy₂
  have eq := agree'.injection.1.1.2 d' y₂ y' hdy₂ hdy'
  have hyy : Rd_entry_d y y' π := eq ▸ hyy₂
  -- 只要求原有限幂的幂集；目标幂集由所属初等图搬运。
  obtain ⟨v, power⟩ := powers m₀ d₀ ((numbers.image m).mpr ⟨n, hn, hnm⟩) ds
  obtain ⟨v', hv', hvv⟩ := map.1.1.2.2 v.val v.property
  let ρ : Env (smdl_structure_l I (R := T) mx.2.1) 2 := ⟨Fin.cases d₀ (fun _ => v), fun _ => d₀⟩
  let η : Env (smdl_structure_l I (R := T') my.2.1) 2 := ⟨Fin.cases d₁ (fun _ => ⟨v', hv'⟩), fun _ => d₁⟩
  have power' := (Formula.satisfies_isPowerSet_iff η (.bound 1) .newest).mp
    ((smap_source_l I hZF hω mx my map (Formula.isPowerSet (.bound 1) .newest)
      (by simp -implicitDefEqProofs [Formula.isPowerSet, Definitional.Formula.FreeClosed]) ρ η
      (Fin.cases hdd (fun _ => hvv))).mp ((Formula.satisfies_isPowerSet_iff ρ (.bound 1) .newest).mpr power))
  have theory' := theory.map_l I hZF hω parent parent' copy
  obtain ⟨P, ft, _, source, measureU⟩ := agree.measure_l I hZF hω parent theory mx.2.1 hN ξ m₀ d₀ u₀
    hn hnm space dc (fn0_function_l (ZF.modelsKP hZF) fi) id rt hdy ⟨v, power⟩ ultra measure
  obtain ⟨Q, ft', _, target, measureV⟩ := agree'.measure_l I hZF hω parent' theory' my.2.1 hN' ξ' m₁ d₁ u₁
    hn hnm' space' ec (fn0_function_l (ZF.modelsKP hZF) fi') id' rt' hdy' ⟨⟨v', hv'⟩, power'⟩ ultra' measure'
  have dom s x (hsx : Rd_entry_d s x t) := (agree.predecessors d y hdy x).mpr
    ⟨s, ((dc s).mp ((rt.2 s x).mp hsx).1).2, ((rt.2 s x).mp hsx).2⟩
  have onto x (hx : Rd_entry_d x y R) : ∃ s, Rd_entry_d s x t := by
    obtain ⟨s, hsd, hsx⟩ := (agree.predecessors d y hdy x).mp hx
    have hs := (dc s).mpr ⟨agree.domain s (agree.injection.1.input_mem_of_pairMember hsx), hsd⟩
    exact ⟨s, (rt.2 s x).mpr ⟨hs, hsx⟩⟩
  have dom' s x (hsx : Rd_entry_d s x t') := (agree'.predecessors d' y' hdy' x).mpr
    ⟨s, ((ec s).mp ((rt'.2 s x).mp hsx).1).2, ((rt'.2 s x).mp hsx).2⟩
  have measures (A A' B B' : M.Domain) :=
    er_copy_measure_l hZF (A := A) (A' := A') (B := B) (B' := B') hω mx my map ext agree agree' hn hnm space hdd hdy hdy' dc ec
      (fn0_function_l (ZF.modelsKP hZF) fi) (fn0_function_l (ZF.modelsKP hZF) fi') id id' rt rt'
      hf hbb value value' unique bounded bounded' measure measure' maps
  have py : Rf_ext_d I Y S := copy.extensional_l hZF hω parent parent' px
  have collection' := (sc_collection_iff_l I hZF hω parent parent'
    (px.native_l I parent.2.1) (py.native_l I parent'.2.1) copy).mp collection
  have small₀ := small n m d y hn hnm space hdy
  have small₁ := (copy.small_l I hZF hω parent parent' hyy).mp small₀
  obtain ⟨K, j, fK, spec, embedding, lift⟩ := rc_copy_embedding_l hZF hω parent parent' copy px theory
    (collection.uniform_l I small₀) (collection'.uniform_l I small₁) hyy
    (fn0_of_function_l (ZF.modelsKP hZF) ft) (fn0_of_function_l (ZF.modelsKP hZF) ft') onto dom dom'
    family family' source target measureU measureV measures quotient quotient'
  obtain ⟨classes, representatives⟩ := rc_copy_class_l I hZF.1 measureU.base measureV.base
    quotient.map quotient'.map fK spec embedding.1.1 lift
  have frame : Er_frame_d I ω L N T ξ.val f.val z X R k a o n m b d u D i t y U G p C W :=
    ⟨hn, fa, hnm, fn, graph, space, value, dc, fi, id, rt, hdy, measure, family, quotient⟩
  have frame' : Er_frame_d I ω L' N' T' ξ'.val f'.val z' Y S k' a' o' n m' b' d' u' E i' t' y' V H q C' W' :=
    ⟨hn, fa', hnm', fn', graph', space', value', ec, fi', id', rt', hdy', measure', family', quotient'⟩
  have raw_classes (B A : M.Domain) : Rd_entry_d B A j ↔ Er_class_d I ω L N T ξ.val f.val z X R k
      L' N' T' ξ'.val f'.val z' Y S k' π σ a a' B A :=
    (classes B A).trans ((and_iff_right assign).symm.trans
      (Er_class_d.read_l hZF numbers numbers' ex ey ξ f ξ' f' actual.measures.function actual'.measures.function
        agree.injection.1.1 agree'.injection.1.1 frame frame').symm)
  have ft₀ := fn0_of_function_l (ZF.modelsKP hZF) ft
  have ft₁ := fn0_of_function_l (ZF.modelsKP hZF) ft'
  let y₀ : (smdl_structure_l I (R := R) parent.2.1).Domain := ⟨y, copy.1.1.input_mem_of_pairMember hyy⟩
  let y₁ : (smdl_structure_l I (R := S) parent'.2.1).Domain := ⟨y', copy.1.1.output_mem_of_pairMember hyy⟩
  obtain ⟨j₀, embed₀, constants₀⟩ := rc_constant_embedding_l hZF hω parent px theory y₀
    (collection.uniform_l I small₀) ft₀ dom source measureU
    ((rc_family_native_l I parent.2.1 (px.native_l I parent.2.1) y₀ ft₀).mp family) quotient
  obtain ⟨j₁, embed₁, constants₁⟩ := rc_constant_embedding_l hZF hω parent' py theory' y₁
    (collection'.uniform_l I small₁) ft₁ dom' target measureV
    ((rc_family_native_l I parent'.2.1 (py.native_l I parent'.2.1) y₁ ft₁).mp family') quotient'
  have points₀ x B : Rd_entry_d x B j₀ ↔ M.mem x X ∧
      ∃ g, Fn0_d D X g ∧ M.mem g B ∧ Rs_const_d D x g ∧ Rd_entry_d g B p := by
    constructor
    · intro hxB
      obtain ⟨hx, g, hg, constant, gp⟩ := (constants₀ x B).mp hxB
      exact ⟨hx, g, quotient.map.functions g hg, quotient.map.representative_l I measureU.base gp, constant, gp⟩
    · rintro ⟨hx, g, _, _, constant, gp⟩
      exact (constants₀ x B).mpr ⟨hx, g, quotient.map.projection.input_mem_of_pairMember gp, constant, gp⟩
  have points₁ x B : Rd_entry_d x B j₁ ↔ M.mem x Y ∧
      ∃ g, Fn0_d E Y g ∧ M.mem g B ∧ Rs_const_d E x g ∧ Rd_entry_d g B q := by
    constructor
    · intro hxB
      obtain ⟨hx, g, hg, constant, gp⟩ := (constants₁ x B).mp hxB
      exact ⟨hx, g, quotient'.map.functions g hg, quotient'.map.representative_l I measureV.base gp, constant, gp⟩
    · rintro ⟨hx, g, _, _, constant, gp⟩
      exact (constants₁ x B).mpr ⟨hx, g, quotient'.map.projection.input_mem_of_pairMember gp, constant, gp⟩
  have coordinate B A (htB : Rd_entry_d t B p) (htA : Rd_entry_d t' A q) : Rd_entry_d B A j := by
    obtain ⟨g, hg, htg⟩ := fK.2.2 t (quotient.map.projection.input_mem_of_pairMember htB)
    have eq := (((spec t g).mp htg).2.2).coordinate_l hZF hω parent parent' copy px hyy ft₁
      (quotient'.map.functions g hg) onto dom'
    exact lift t t' B A (eq ▸ htg) htB htA
  refine ⟨D, E, t, t', y, y', U, V, G, H, p, q, C, C', W, W', K, j, j₀, j₁,
    fn0_of_function_l (ZF.modelsKP hZF) ft, fn0_of_function_l (ZF.modelsKP hZF) ft', hyy,
    ⟨n, m, b, d, u, i, frame⟩, ⟨n, m', b', d', u', i', frame'⟩,
    fK, spec, embedding, lift, classes, raw_classes, representatives, embed₀, embed₁, points₀, points₁, ?_, coordinate⟩
  -- 常值代表的实际复制给出两条原模型嵌入之间的交换方块。
  intro x x' B A hxx hxB
  obtain ⟨_, g, hg, constant, gp⟩ := (constants₀ x B).mp hxB
  obtain ⟨g', hg', hgg⟩ := fK.2.2 g hg
  obtain ⟨A', _, gq⟩ := quotient'.map.projection.2.2 g' hg'
  have constant' := (((spec g g').mp hgg).2.2).constant_l hZF hω parent parent' copy px hyy hxx
    ft₀ ft₁ onto dom' constant
  have hxA := (constants₁ x' A').mpr ⟨copy.1.1.output_mem_of_pairMember hxx, g', hg', constant', gq⟩
  have hBA := lift g g' B A' hgg gp gq
  exact ⟨fun h => embedding.1.1.1.2 B A' A hBA h ▸ hxA,
    fun h => embed₁.1.1.1.2 x' A' A hxA h ▸ hBA⟩

end YesMetaZFC.SetTheory.LargeCardinal
