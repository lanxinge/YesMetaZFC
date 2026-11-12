import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawGraphSyntax
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationCrossBounded
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.Model.SetTheory.Relations.RecordImage

/-! # 对象码极限中新成员的完整有界覆盖

原常值与任意新成员先移到共同支撑，再将同一个中间代表处处有界化。
所得函数码由原乘积和子集闭包回收到所属切片，原对象码图进入同一极限。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_graph_d.bounded_l {ω c' Y S Γ H k N T z L J O Z A p V W r C W'
    b D₀ a₀ f₀ H₀ E : M.Domain}
    (hω : M.IsOmega ω) (model : Smdl_d I c' Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I ω Y S)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (U w ξ ℓ e a : (smdl_structure_l I (R := T) nx).Domain)
    (numbers : Rr_layer_d I ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l I (R := T) nx).Domain,
      (smdl_structure_l I (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l I (R := T) nx).IsPowerSetOf p d)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d I N T U.val) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d I Y S H) (hξ : (smdl_structure_l I (R := T) nx).mem ξ U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (products : ∀ m d : (smdl_structure_l I (R := T) nx).Domain,
      (smdl_structure_l I (R := T) nx).mem m w → Ep_space_d ξ m d →
      ∃ P : (smdl_structure_l I (R := T) nx).Domain, (smdl_structure_l I (R := T) nx).mem P U ∧
        (smdl_structure_l I (R := T) nx).IsCartesianProduct (kp_pair_l hN) P d a)
    (h : Er_graph_d I ω L N T ξ.val ℓ.val e.val z Y S k J O Z A p V W)
    (diagram : Di_system_d J O A p V W) (limit : Di_limit_d A p V W r C W') (hab : Rd_entry_d a.val b k)
    (ff₀ : Fn0_d D₀ Y f₀) (constant : Rs_const_d D₀ b f₀) (fv : Ep_repr_d r a₀ f₀ H₀)
    (edge : Rd_entry_d E H₀ W') (loc : It_local_d I w.val N T ξ.val ℓ.val e.val) :
    ∃ α, ∃ m α' d f : (smdl_structure_l I (R := T) nx).Domain, ∃ D F g,
      M.mem α J ∧ Rr_finite_d I ω L N T z α α'.val ∧ (smdl_structure_l I (R := T) nx).mem m w ∧
      Fn0_d m ℓ α' ∧ Ep_space_d ξ m d ∧ (smdl_structure_l I (R := T) nx).mem f U ∧ Fn0_d d a f ∧
      (∀ s, M.mem s D ↔ M.mem s N ∧ Rd_entry_d s d.val T) ∧ Fn0_d D Γ F ∧
      (∀ s v : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d s.val v.val F ↔ Rd_entry_d s v f) ∧
      Cp0_d D Γ Y F k g ∧ Ep_repr_d r α g E := by
  obtain ⟨u, huE⟩ := (limit.range E).mp (limit.bounded E H₀ edge).1
  obtain ⟨v, B₀, pv, hfB₀, hvH⟩ := fv
  obtain ⟨α, x, y, hxα, hyα, hux, hvy, hxy⟩ := (limit.relation u v E H₀ huE hvH).mp edge
  obtain ⟨P, px, o, C₁, W₁, hαo, pair, hPC⟩ := h.label_l hxα
  obtain ⟨Q, py, atQ⟩ := h.label_l hyα
  obtain ⟨_, table⟩ := h.codes
  have hQC := (ep_at_read_l table hαo pair).mp atQ
  have relation := (ep_rel_read_l table hαo pair).mp ((h.relation_l px py).mp hxy).2.2
  obtain ⟨q, identity, _⟩ := smap_identity_l I hZF (X := Y) (c := c') hω
  obtain ⟨n, m, α', d, μ, hn, fα, hnm, fn, ga, fa, ds, hd, _,
    D, _, t, d₀, _, U₀, G, s, C₂, W₂, dc, _, _, rt, ft, hdd, _, _, ultra, _, family, quotient⟩ :=
    (h.components α o hαo).read_l hZF hω model theory model identity nx hN U w ξ ℓ e numbers finite powers
      carrier ownerClosed fk image pred closed hξ length loc
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair quotient.code.1
  -- 第一张常值代表沿实际边复合；其定义域由函数性唯一识别。
  obtain ⟨D₁, D₂, t₀, f', _, hfQ, pull⟩ := h.lift_l hZF.1 pv py hvy hfB₀
  have fp := quotient.map.member_l I hZF.1 ultra.base hQC hfQ
  have ff := quotient.map.functions f' (quotient.map.projection.input_mem_of_pairMember fp)
  have eq := pull.1.domain_eq_l hZF.1 ff
  subst D₂
  -- 任一输入的复合见证都落在原常值代表的真实定义域。
  have fc : Rs_const_d D b f' := by
    intro s hs
    obtain ⟨v, _, y, _, _, hvy, hsy⟩ := pull.2 s hs
    have hv₀ := (ff₀.bound_l hvy).1
    have value := constant v hv₀
    have ey := ff₀.2.2 v hv₀ y (ff₀.bound_l hvy).2 b (ff₀.bound_l value).2 hvy value
    exact ey ▸ hsy
  let d' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨d₀, fk.1.output_mem_of_pairMember hdd⟩
  let b' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨b, fk.1.output_mem_of_pairMember hab⟩
  have domain s x (hsx : Rd_entry_d s x t) := (pred d.val d₀ hdd x).mpr
    ⟨s, ((dc s).mp ((rt.2 s x).mp hsx).1).2, ((rt.2 s x).mp hsx).2⟩
  have codes := (rc_family_native_l I model.2.1 (ext.native_l I model.2.1) d' ft).mp family
  obtain ⟨g, hg, gp, bound, _⟩ := rc_bounded_representative_l hZF hω model ext theory d' ft domain
    ultra.base ultra.proper codes quotient ⟨b'.property, f', quotient.map.projection.input_mem_of_pairMember fp, fc, fp⟩ relation
  obtain ⟨P₀, hP₀, product⟩ := products m d ((numbers.image m.val).mpr ⟨n, hn, hnm⟩) ds
  obtain ⟨f, F, hf, ff, fF, graph, comp⟩ := (rr_cross_functions_l hZF nx model.2.1 hN
    (ext.native_l I model.2.1) U d a P₀ finite.transitive carrier fk image pred closed hP₀ product d' b' hdd hab dc rt codes g).mp ⟨hg, bound⟩
  obtain ⟨E', _, hxE⟩ := limit.projection.2.1 x (h.projection.bound_l hxα).1
  have eq := limit.commute_l diagram hux huE hxE
  exact ⟨α, m, α', d, f, D, F, g, (h.projection.bound_l hxα).2, ⟨n, m.val, hn, fα, hnm, fn, ga⟩,
    (numbers.image m.val).mpr ⟨n, hn, hnm⟩, fa, ds, hf, ff, dc, fF, graph, comp,
    x, P, px, quotient.map.representative_l I ultra.base gp, eq.symm ▸ hxE⟩

/-- 处处有界的任意代表在同一个原关系极限中确实属于原常值像。 -/
theorem Er_graph_d.bound_mem_l {ω c X R c' Y S q Γ H k N T z L J O Z A p V W r C W'
    b D₀ a₀ f₀ H₀ α g E : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (U w ξ ℓ e : (smdl_structure_l I (R := T) nx).Domain)
    (numbers : Rr_layer_d I ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l I (R := T) nx).Domain,
      (smdl_structure_l I (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l I (R := T) nx).IsPowerSetOf p d)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d I N T U.val) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d I Y S H) (hξ : (smdl_structure_l I (R := T) nx).mem ξ U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (h : Er_graph_d I ω L N T ξ.val ℓ.val e.val z Y S k J O Z A p V W)
    (diagram : Di_system_d J O A p V W) (limit : Di_limit_d A p V W r C W') (hb : M.mem b Y)
    (ff₀ : Fn0_d D₀ Y f₀) (constant : Rs_const_d D₀ b f₀) (fv : Ep_repr_d r a₀ f₀ H₀)
    (bound : ∀ s y, Rd_entry_d s y g → Rd_entry_d y b S) (gv : Ep_repr_d r α g E)
    (loc : It_local_d I w.val N T ξ.val ℓ.val e.val) : Rd_entry_d E H₀ W' := by
  obtain ⟨u, B, pu, hgB, huE⟩ := gv
  obtain ⟨v, B₀, pv, hfB₀, hvH⟩ := fv
  obtain ⟨β, x, y, hxβ, hyβ, hux, hvy⟩ := diagram.common_l (limit.projection.bound_l huE).1 (limit.projection.bound_l hvH).1
  obtain ⟨P, px, o, C₁, W₁, hβo, pair, hPC⟩ := h.label_l hxβ
  obtain ⟨Q, py, atQ⟩ := h.label_l hyβ
  obtain ⟨_, table⟩ := h.codes
  have hQC := (ep_at_read_l table hβo pair).mp atQ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
    D, _, _, _, _, U₀, G, s, C₂, W₂, _, _, _, _, _, _, _, _, ultra, _, _, quotient⟩ :=
    (h.components β o hβo).read_l hZF hω mx theory model hq nx hN U w ξ ℓ e numbers finite powers
      carrier ownerClosed fk image pred closed hξ length loc
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair quotient.code.1
  obtain ⟨D₁, D₂, t, g', _, hgP, pull⟩ := h.lift_l hZF.1 pu px hux hgB
  obtain ⟨D₃, D₄, t₀, f', _, hfQ, pull₀⟩ := h.lift_l hZF.1 pv py hvy hfB₀
  have gp := quotient.map.member_l I hZF.1 ultra.base hPC hgP
  have fp := quotient.map.member_l I hZF.1 ultra.base hQC hfQ
  have fg := quotient.map.functions g' (quotient.map.projection.input_mem_of_pairMember gp)
  have ff := quotient.map.functions f' (quotient.map.projection.input_mem_of_pairMember fp)
  have eq := pull.1.domain_eq_l hZF.1 fg
  subst D₂
  have eq := pull₀.1.domain_eq_l hZF.1 ff
  subst D₄
  have fc : Rs_const_d D b f' := by
    intro z hz
    obtain ⟨v, _, y, _, _, hvy, hzy⟩ := pull₀.2 z hz
    have hv₀ := (ff₀.bound_l hvy).1
    have value := constant v hv₀
    exact (ff₀.2.2 v hv₀ y (ff₀.bound_l hvy).2 b (ff₀.bound_l value).2 hvy value) ▸ hzy
  have bounded z y (hzy : Rd_entry_d z y g') : Rd_entry_d y b S := by
    obtain ⟨v, _, y', hy', _, hvy, hzy'⟩ := pull.2 z (fg.bound_l hzy).1
    exact fg.2.2 z (fg.bound_l hzy).1 y' hy' y (fg.bound_l hzy).2 hzy' hzy ▸ bound v y' hvy
  have relation := (quotient.relation g' f' P Q gp fp).mpr ⟨D, ultra.base.top, fun z hz => by
    obtain ⟨y, hy, hzy⟩ := fg.2.1 z hz
    exact ⟨y, hy, b, hb, hzy, fc z hz, bounded z y hzy⟩⟩
  exact (limit.relation u v E H₀ huE hvH).mpr ⟨β, x, y, hxβ, hyβ, hux, hvy,
    (h.relation_l px py).mpr ⟨(h.projection.bound_l hxβ).1, (h.projection.bound_l hyβ).1,
      (ep_rel_read_l table hβo quotient.code.1).mpr relation⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原函数在对象码极限中的实际求值

由原支撑码识别规范分量，展开同一个原函数并复合共同层实现。
所得代表属于已构造的完整代表族，因此其商类与极限值均实际存在。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_graph_d.bounded_value_l {ω c' Y S Γ H k N T z L J O Z A p V W r C W' α b : M.Domain}
    (hω : M.IsOmega ω) (model : Smdl_d I c' Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I ω Y S)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (U w ξ ℓ e a : (smdl_structure_l I (R := T) nx).Domain)
    (numbers : Rr_layer_d I ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l I (R := T) nx).Domain,
      (smdl_structure_l I (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l I (R := T) nx).IsPowerSetOf p d)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d I N T U.val) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d I Y S H) (hξ : (smdl_structure_l I (R := T) nx).mem ξ U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (h : Er_graph_d I ω L N T ξ.val ℓ.val e.val z Y S k J O Z A p V W)
    (limit : Di_limit_d A p V W r C W') (hab : Rd_entry_d a.val b k)
    (m α' d f : (smdl_structure_l I (R := T) nx).Domain)
    (hα : M.mem α J) (code : Rr_finite_d I ω L N T z α α'.val)
    (fa : Fn0_d m ℓ α') (space : Ep_space_d ξ m d)
    (hf : (smdl_structure_l I (R := T) nx).mem f U) (fn : Fn0_d d a f)
    (loc : It_local_d I w.val N T ξ.val ℓ.val e.val) :
    ∃ D F g E, (∀ s, M.mem s D ↔ M.mem s N ∧ Rd_entry_d s d.val T) ∧ Fn0_d D Γ F ∧
      (∀ s v : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d s.val v.val F ↔ Rd_entry_d s v f) ∧
      Cp0_d D Γ Y F k g ∧ Ep_repr_d r α g E ∧
      ∀ s y, Rd_entry_d s y g → Rd_entry_d y b S := by
  obtain ⟨_, table⟩ := h.codes
  obtain ⟨o, _, hαo⟩ := table.2.1 α hα
  obtain ⟨q, identity, _⟩ := smap_identity_l I hZF (X := Y) (c := c') hω
  obtain ⟨n, m', β, d₀, _, hn, fα, hnm, fβ, ga, fb, space₀, _, _,
    D, _, t, y, _, U₀, G, s, C₀, W₀, dc, _, _, rt, ft, hdd, _, _, ultra, _, family, quotient⟩ :=
    (h.components α o hαo).read_l hZF hω model theory model identity nx hN U w ξ ℓ e numbers finite powers
      carrier ownerClosed fk image pred closed hξ length loc
  have eq : β = α' := Subtype.ext
    ((show Rr_finite_d I ω L N T z α β.val from ⟨n, m'.val, hn, fα, hnm, fβ, ga⟩).unique_l
      hZF numbers hN.1 code)
  subst β
  have eq := fb.domain_eq_l hN.1 fa
  subst m'
  have eq := hN.1.eq_of_same_members d₀ d (fun x => (space₀ x).trans (space x).symm)
  subst d₀
  have haU := ((carrier a.val).mp (fk.1.input_mem_of_pairMember hab)).2
  obtain ⟨D', B, F, dc', bc, fF, graph⟩ := smdl_graph_l hZF nx hN.1 d a f fn
  have eq := hZF.1.eq_of_same_members D' D (fun x => (dc' x).trans (dc x).symm)
  subst D'
  have fF := fF.mono_target_l (fun v hv => (carrier v).mpr ⟨((bc v).mp hv).1,
    finite.transitive a haU ⟨v, ((bc v).mp hv).1⟩ ((bc v).mp hv).2⟩)
  let d' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨y, fk.1.output_mem_of_pairMember hdd⟩
  let a' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨b, fk.1.output_mem_of_pairMember hab⟩
  have codes := (rc_family_native_l I model.2.1 (ext.native_l I model.2.1) d' ft).mp family
  obtain ⟨v, hv, hfv⟩ := fk.1.2.2 f.val ((carrier f.val).mpr ⟨f.property, hf⟩)
  let f' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨v, hv⟩
  have moved := rr_native_function_l I nx model.2.1 hN.1 (ext.native_l I model.2.1) U finite.transitive
    carrier fk pred d a f d' a' f' hdd hab hfv fn
  have domain s x (hsx : Rd_entry_d s x t) := (pred d.val y hdd x).mpr
    ⟨s, ((dc s).mp ((rt.2 s x).mp hsx).1).2, ((rt.2 s x).mp hsx).2⟩
  obtain ⟨g, fg, decode⟩ := smdl_function_l hZF model.2.1 (ext.native_l I model.2.1) d' a' f' moved.1 ft domain
  have hg := (codes g).mpr ⟨fg, a', f', moved.1, decode⟩
  have comp : Cp0_d D Γ Y F k g := ⟨fg, fun s hs => by
    obtain ⟨v, hv, hsv⟩ := fF.2.1 s hs
    obtain ⟨y, hy, hvy⟩ := fk.1.2.2 v hv
    obtain ⟨x, hx, hsx⟩ := ft.2.1 s hs
    let s' : (smdl_structure_l I (R := T) nx).Domain := ⟨s, ((dc s).mp hs).1⟩
    let v' : (smdl_structure_l I (R := T) nx).Domain := ⟨v, ((carrier v).mp hv).1⟩
    exact ⟨v, hv, y, hy, hsv, hvy, (decode s ⟨x, hx⟩ ⟨y, hy⟩ hsx).mpr
      ((moved.2 s' v' ⟨x, hx⟩ ⟨y, hy⟩ ((rt.2 s x).mp hsx).2 hvy).mp ((graph s' v').mp hsv))⟩⟩
  have bound s y (hsy : Rd_entry_d s y g) : Rd_entry_d y b S := by
    obtain ⟨x, hx, hsx⟩ := ft.2.1 s (fg.bound_l hsy).1
    exact (moved.1.bound_l ((decode s ⟨x, hx⟩ ⟨y, (fg.bound_l hsy).2⟩ hsx).mp hsy)).2
  obtain ⟨B₀, hB₀, gp⟩ := quotient.map.projection.2.2 g hg
  obtain ⟨u, pair⟩ := (I).total α B₀
  obtain ⟨E, _, huE⟩ := limit.projection.2.1 u ((h.nodes u).mpr ⟨α, B₀, pair, o, C₀, W₀, hαo, quotient.code.1, hB₀⟩)
  exact ⟨D, F, g, E, dc, fF, graph, comp, ⟨u, B₀, pair, quotient.map.representative_l I ultra.base gp, huE⟩, bound⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原池节点在对象码极限中的求值公式

节点按原配对读取支撑码和函数码。函数定义域及其对象码图均由原对象
确定；公式不把原函数码误当作背景函数图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Er_eval_d (ω L N T z Γ Y k r u E : M.Domain) : Prop := ∃ α a f d D F g,
  Rr_finite_d I ω L N T z α a ∧ Rf_pair_d I N T u a f ∧ Rf_fun_d I N T d f ∧
  (∀ s, M.mem s D ↔ M.mem s N ∧ Rd_entry_d s d T) ∧ Fn0_d D Γ F ∧
  (∀ s v, M.mem s N → M.mem v N → (Rd_entry_d s v F ↔ Rf_val_d I N T s v f)) ∧
  Cp0_d D Γ Y F k g ∧ Ep_repr_d r α g E

def er_eval_m {n} (ω L N T z Γ Y k r u E : Term n) : Formula 1 n := set[n] ⟪∃ α a f d D F g,
  ⌜rr_finite_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜N⌝ₛ, ⌜T⌝ₛ, ⌜z⌝ₛ, α, a) ∧
  ⌜rf_pair_m (𝒞 := kpair_convention_l)⌝ₚ(⌜N⌝ₛ, ⌜T⌝ₛ, ⌜u⌝ₛ, a, f) ∧
  ⌜rf_fun_m (𝒞 := kpair_convention_l)⌝ₚ(⌜N⌝ₛ, ⌜T⌝ₛ, d, f) ∧
  (∀ s, s ∈ D ↔ s ∈ ⌜N⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(s, d, ⌜T⌝ₛ)) ∧ ⌜fn0_m⌝ₚ(D, ⌜Γ⌝ₛ, F) ∧
  (∀ s ∈ ⌜N⌝ₛ, ∀ v ∈ ⌜N⌝ₛ, ⌜rd_entry0_m⌝ₚ(s, v, F) ↔
    ⌜rf_val_m (𝒞 := kpair_convention_l)⌝ₚ(⌜N⌝ₛ, ⌜T⌝ₛ, s, v, f)) ∧
  ⌜cp0_m⌝ₚ(D, ⌜Γ⌝ₛ, ⌜Y⌝ₛ, F, ⌜k⌝ₛ, g) ∧ ⌜ep_repr_m⌝ₚ(⌜r⌝ₛ, α, g, ⌜E⌝ₛ)⟫
derive_free_closed er_eval_m

theorem er_eval_sat_l (ext : Extensional M) {n} (ρ : Env M n) (ω L N T z Γ Y k r u E : Term n) :
    Formula.satisfies ρ (er_eval_m ω L N T z Γ Y k r u E) ↔
      Er_eval_d I (ω.eval ρ) (L.eval ρ) (N.eval ρ) (T.eval ρ) (z.eval ρ) (Γ.eval ρ)
        (Y.eval ρ) (k.eval ρ) (r.eval ρ) (u.eval ρ) (E.eval ρ) := by
  simp only [er_eval_m, Er_eval_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rr_finite_sat_l I ext, rf_pair_sat_l I, rf_fun_sat_l I, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l ext, fn0_sat_l ext,
    Formula.satisfies_forallMem_iff, rf_val_sat_l I, cp0_sat_l ext, ep_repr_sat_l ext, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨α, a, f, d, D, F, g, ha, pair, fn, dc, fF, graph, comp, value⟩ =>
    ⟨α, a, f, d, D, F, g, ha, pair, fn, dc, fF, (fun s v hs hv => graph s hs v hv), comp, value⟩,
    fun ⟨α, a, f, d, D, F, g, ha, pair, fn, dc, fF, graph, comp, value⟩ =>
    ⟨α, a, f, d, D, F, g, ha, pair, fn, dc, fF, (fun s hs v hv => graph s v hs hv), comp, value⟩⟩

variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_eval_d.read_l {ω L N T z Γ Y k r α E w : M.Domain}
    (numbers : Rr_layer_d Kp ω N T w z)
    (ext : Extensional (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩))
    (u a f d β : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Domain)
    (ca : Rr_finite_d Kp ω L N T z α a.val) (fn : Fn0_d d β f)
    (pair : KPair_d (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩) u a f)
    (value : Er_eval_d Kp ω L N T z Γ Y k r u.val E) :
    ∃ D F g, (∀ s, M.mem s D ↔ M.mem s N ∧ Rd_entry_d s d.val T) ∧ Fn0_d D Γ F ∧
      (∀ s v : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Domain, Rd_entry_d s.val v.val F ↔ Rd_entry_d s v f) ∧
      Cp0_d D Γ Y F k g ∧ Ep_repr_d r α g E := by
  let N₀ := smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩
  obtain ⟨α', a₀, f₀, d₀, D, F, g, ca', pair', fn', dc, fF, graph, comp, ev⟩ := value
  let a' : N₀.Domain := ⟨a₀, (pair'.bounds_l Kp).2.1⟩
  let f' : N₀.Domain := ⟨f₀, (pair'.bounds_l Kp).2.2⟩
  obtain ⟨ea, ef⟩ := kpair_injective_l N₀ ((rf_pair_native_l Kp _ ext u a' f').mp pair') pair
  have ea : a₀ = a.val := congrArg (fun x : N₀.Domain => x.val) ea
  have ef : f₀ = f.val := congrArg (fun x : N₀.Domain => x.val) ef
  subst a₀ f₀
  have eq := ca'.input_unique_l hZF numbers ca
  subst α'
  let d' : N₀.Domain := ⟨d₀, fn'.elim (fun hd _ => hd)⟩
  obtain ⟨B, fb⟩ := (rf_fun_native_l Kp _ ext d' f).mp fn'
  have eq : d₀ = d.val := congrArg (fun x : N₀.Domain => x.val) (fb.domain_eq_l ext fn)
  subst d₀
  exact ⟨D, F, g, dc, fF, fun s v => (graph s.val v.val s.property v.property).trans
    (rf_val_native_l Kp _ ext s v f), comp, ev⟩

theorem Er_eval_d.write_l {ω L N T z Γ Y k r α D F g E : M.Domain}
    (nx : ∃ x, M.mem x N) (ext : Extensional (smdl_structure_l Kp (R := T) nx))
    (u a f d β : (smdl_structure_l Kp (R := T) nx).Domain)
    (ca : Rr_finite_d Kp ω L N T z α a.val) (fn : Fn0_d d β f)
    (pair : KPair_d (smdl_structure_l Kp (R := T) nx) u a f)
    (dc : ∀ s, M.mem s D ↔ M.mem s N ∧ Rd_entry_d s d.val T) (fF : Fn0_d D Γ F)
    (graph : ∀ s v : (smdl_structure_l Kp (R := T) nx).Domain, Rd_entry_d s.val v.val F ↔ Rd_entry_d s v f)
    (comp : Cp0_d D Γ Y F k g) (value : Ep_repr_d r α g E) : Er_eval_d Kp ω L N T z Γ Y k r u.val E :=
  ⟨α, a.val, f.val, d.val, D, F, g, ca, (rf_pair_native_l Kp nx ext u a f).mpr pair,
    (rf_fun_native_l Kp nx ext d f).mpr ⟨β, fn⟩, dc, fF,
    fun s v hs hv => (graph ⟨s, hs⟩ ⟨v, hv⟩).trans (rf_val_native_l Kp nx ext ⟨s, hs⟩ ⟨v, hv⟩ f).symm, comp, value⟩

/-- 原池函数的共同层像直接解释同一个求值代表；无需另给函数图对应假设。 -/
theorem Er_eval_d.function_l {ω L N T w z Γ Y S k r α D t y b' f' E : M.Domain}
    (numbers : Rr_layer_d Kp ω N T w z)
    (en : Extensional (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩))
    (ny : ∃ y, M.mem y Y) (ey : Extensional (smdl_structure_l Kp (R := S) ny))
    (U u a f d b : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Domain)
    (trans : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).TransitiveSet U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (fk : M.IsSetInjectionFromTo Kp k Γ Y)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (ca : Rr_finite_d Kp ω L N T z α a.val) (ff : Fn0_d d b f)
    (pair : KPair_d (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩) u a f)
    (dc : ∀ s, M.mem s D ↔ M.mem s N ∧ Rd_entry_d s d.val T)
    (ft : Fn0_d D Y t) (rt : M.IsRestrictionOf Kp t k D)
    (hdy : Rd_entry_d d.val y k) (hbb : Rd_entry_d b.val b' k) (hff : Rd_entry_d f.val f' k)
    (value : Er_eval_d Kp ω L N T z Γ Y k r u.val E) :
    Rf_fun_d Kp Y S y f' ∧ ∃ g, Rc_graph_d Kp Y S t f' g ∧ Ep_repr_d r α g E := by
  let d₁ : (smdl_structure_l Kp (R := S) ny).Domain := ⟨y, fk.1.output_mem_of_pairMember hdy⟩
  let b₁ : (smdl_structure_l Kp (R := S) ny).Domain := ⟨b', fk.1.output_mem_of_pairMember hbb⟩
  let f₁ : (smdl_structure_l Kp (R := S) ny).Domain := ⟨f', fk.1.output_mem_of_pairMember hff⟩
  have ext : Rf_ext_d Kp Y S := fun x hx y hy same => congrArg Subtype.val
    (ey.eq_of_same_members ⟨x, hx⟩ ⟨y, hy⟩ (fun v => same v.val v.property))
  have moved := rr_native_function_l Kp ⟨w, numbers.member⟩ ny en ey U trans carrier fk pred
    d b f d₁ b₁ f₁ hdy hbb hff ff
  have fn := (rf_fun_native_l Kp ny ey d₁ f₁).mpr ⟨b₁, moved.1⟩
  obtain ⟨D₀, F₀, g, dc₀, _, graph, comp, rep⟩ := value.read_l hZF numbers en u a f d b ca ff pair
  have eq := hZF.1.eq_of_same_members D₀ D (fun s => (dc₀ s).trans (dc s).symm)
  subst D₀
  refine ⟨fn, g, ?_, rep⟩
  intro s x y hsx
  obtain ⟨v, hv, z, hz, hsv, hvz, hsz⟩ := comp.2 s (ft.bound_l hsx).1
  let s₀ : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Domain := ⟨s, ((dc s).mp (ft.bound_l hsx).1).1⟩
  let v₀ : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Domain := ⟨v, ((carrier v).mp hv).1⟩
  let x₁ : (smdl_structure_l Kp (R := S) ny).Domain := ⟨x, (ft.bound_l hsx).2⟩
  let z₁ : (smdl_structure_l Kp (R := S) ny).Domain := ⟨z, hz⟩
  have val := (rf_val_native_l Kp ny ey x₁ z₁ f₁).mpr
    ((moved.2 s₀ v₀ x₁ z₁ ((rt.2 s x).mp hsx).2 hvz).mp ((graph s₀ v₀).mp hsv))
  constructor
  · intro h
    exact (fn0_function_l (ZF.modelsKP hZF) comp.1).1.2 s z y hsz h ▸ val
  · intro h
    exact fn.unique_l Kp ext val h ▸ hsz

end YesMetaZFC.SetTheory.LargeCardinal
