import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyMaps
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawGraphSyntax
import YesMetaZFC.Model.SetTheory.Relations.LayerComposition
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull

/-! # 原所属图上有限支撑的实际像

支撑沿原所属图复合，原长度对象的像保证值落在目标字母表。逐点图方程
和单射性同时得到，因此每个原索引均自动产生一个实际目标索引。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_support_image_l {ω c X R c' Y S σ ℓ ℓ' L L' n a : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I c' Y S)
    (map : Smap_d I ω c c' X Y σ) (hℓ : Rd_entry_d ℓ ℓ' σ)
    (length : ∀ x, M.mem x L ↔ M.mem x X ∧ Rd_entry_d x ℓ R)
    (length' : ∀ x, M.mem x L' ↔ M.mem x Y ∧ Rd_entry_d x ℓ' S)
    (fa : Fn0_d n L a) :
    ∃ a', Fn0_d n L' a' ∧ Smap_assign_d I n σ a a' ∧
      (∀ i y, Rd_entry_d i y a' ↔ ∃ x, Rd_entry_d i x a ∧ Rd_entry_d x y σ) ∧
      ((∀ i j x, Rd_entry_d i x a → Rd_entry_d j x a → i = j) ↔
        ∀ i j x, Rd_entry_d i x a' → Rd_entry_d j x a' → i = j) := by
  have fn := fn0_function_l (ZF.modelsKP hZF) (fa.mono_target_l (fun x hx => ((length x).mp hx).1))
  obtain ⟨a', fn', graph⟩ := ZF.exists_compositionFunction hZF I fn map.1.1
  have bound i y (hiy : Rd_entry_d i y a') : M.mem y L' := by
    obtain ⟨_, x, hix, hxy⟩ := (graph i y).mp hiy
    exact (length' y).mpr ⟨map.1.1.output_mem_of_pairMember hxy,
      (map.relation_l I hZF hω mx my hxy hℓ).mp ((length x).mp (fa.bound_l hix).2).2⟩
  have assign : Smap_assign_d I n σ a a' := fun i hi x y hix hxy => (graph i y).mpr ⟨hi, x, hix, hxy⟩
  refine ⟨a', (fn0_of_function_l (ZF.modelsKP hZF) fn').retarget_l bound, assign,
    fun i y => (graph i y).trans ⟨And.right, fun ⟨x, hix, hxy⟩ => ⟨(fa.bound_l hix).1, x, hix, hxy⟩⟩, ?_⟩
  constructor
  · intro injective i j y hiy hjy
    obtain ⟨_, x, hix, hxy⟩ := (graph i y).mp hiy
    obtain ⟨_, z, hjz, hzy⟩ := (graph j y).mp hjy
    exact injective i j x hix (map.1.2 z x y hzy hxy ▸ hjz)
  · intro injective i j x hix hjx
    obtain ⟨y, _, hxy⟩ := map.1.1.2.2 x (fn.output_mem_of_pairMember hix)
    exact injective i j y (assign i (fa.bound_l hix).1 x y hix hxy) (assign j (fa.bound_l hjx).1 x y hjx hxy)

/-- 每个原索引自动取得实际目标支撑及两端规范分量码。 -/
theorem Er_graph_d.copy_index_l
    {ω c N T c' N' T' σ ξ ξ' ℓ ℓ' F F' z z' L L' X R Y S k k'
      J O Z A p V W J' O' Z' A' p' V' W' a : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ) (hℓ : Rd_entry_d ℓ ℓ' σ)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ T)
    (length' : ∀ x, M.mem x L' ↔ M.mem x N' ∧ Rd_entry_d x ℓ' T')
    (source : Er_graph_d I ω L N T ξ ℓ F z X R k J O Z A p V W)
    (target : Er_graph_d I ω L' N' T' ξ' ℓ' F' z' Y S k' J' O' Z' A' p' V' W')
    (ha : M.mem a J) :
    ∃ n a' o o', M.mem n ω ∧ Fn0_d n L a ∧ Fn0_d n L' a' ∧ Smap_assign_d I n σ a a' ∧
      (∀ i y, Rd_entry_d i y a' ↔ ∃ x, Rd_entry_d i x a ∧ Rd_entry_d x y σ) ∧
      M.mem a' J' ∧ Rd_entry_d a o Z ∧ Rd_entry_d a' o' Z' ∧
      Er_code_d I ω L N T ξ F z X R k a o ∧ Er_code_d I ω L' N' T' ξ' F' z' Y S k' a' o' := by
  obtain ⟨n, hn, fa, injective⟩ := (source.indices a).mp ha
  obtain ⟨a', fa', assign, graph, injective'⟩ := er_support_image_l hZF hω mx my map hℓ length length' fa
  have ha' := (target.indices a').mpr ⟨n, hn, fa', injective'.mp injective⟩
  obtain ⟨_, table⟩ := source.codes
  obtain ⟨_, table'⟩ := target.codes
  obtain ⟨o, _, hao⟩ := table.2.1 a ha
  obtain ⟨o', _, hao'⟩ := table'.2.1 a' ha'
  exact ⟨n, a', o, o', hn, fa, fa', assign, graph, ha', hao, hao',
    source.components a o hao, target.components a' o' hao'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系支撑投影的实际复制

先搬运两个支撑的原函数码，再搬运同一个投影定义。目标投影从原函数
实际展开；其定义域覆盖目标有限幂的全部对象码，包含原图像以外的新点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 支撑像及目标支撑单射性唯一确定实际重排图的像。 -/
theorem er_factor_image_l {ω c N T c' N' T' σ : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ) (ext : Rf_ext_d I N T)
    (m n ℓ a b r : (smdl_structure_l I (R := T) mx.2.1).Domain)
    (m' n' ℓ' a' b' r' : (smdl_structure_l I (R := T') my.2.1).Domain)
    (hℓ : Rd_entry_d ℓ.val ℓ'.val σ) (haa : Rd_entry_d a.val a'.val σ) (hbb : Rd_entry_d b.val b'.val σ)
    (fa : Fn0_d m ℓ a) (fb : Fn0_d n ℓ b) (fr : Fn0_d m n r) (factor : Cp0_d m n ℓ r b a)
    (fa' : Fn0_d m' ℓ' a') (fb' : Fn0_d n' ℓ' b') (fr' : Fn0_d m' n' r') (factor' : Cp0_d m' n' ℓ' r' b' a')
    (inj : ∀ i j x, Rd_entry_d i x b' → Rd_entry_d j x b' → i = j) :
    Rd_entry_d m.val m'.val σ ∧ Rd_entry_d n.val n'.val σ ∧ Rd_entry_d r.val r'.val σ := by
  have ext' : Rf_ext_d I N' T' := map.extensional_l hZF hω mx my ext
  have ex := ext.native_l I mx.2.1
  have ey := ext'.native_l I my.2.1
  have domain (x f : (smdl_structure_l I (R := T) mx.2.1).Domain)
      (x' f' : (smdl_structure_l I (R := T') my.2.1).Domain)
      (hff : Rd_entry_d f.val f'.val σ) (fn : Fn0_d x ℓ f) (fn' : Fn0_d x' ℓ' f') : Rd_entry_d x.val x'.val σ := by
    obtain ⟨y, hy, hxy⟩ := map.1.1.2.2 x.val x.property
    have code := (rf_fun_native_l I mx.2.1 ex x f).mpr ⟨ℓ, fn⟩
    have moved := code.map_l I hZF hω mx my map hxy hff
    obtain ⟨B, fy⟩ := (rf_fun_native_l I my.2.1 ey ⟨y, hy⟩ f').mp moved
    exact (show y = x'.val from congrArg Subtype.val (fy.domain_eq_l ey fn')) ▸ hxy
  have hmm := domain m a m' a' haa fa fa'
  have hnn := domain n b n' b' hbb fb fb'
  obtain ⟨R, hR, hrR⟩ := map.1.1.2.2 r.val r.property
  let r₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨R, hR⟩
  let ρ : Env (smdl_structure_l I (R := T) mx.2.1) 6 :=
    ⟨Fin.cases a (Fin.cases b (Fin.cases r (Fin.cases ℓ (Fin.cases n (fun _ => m))))), fun _ => a⟩
  let η : Env (smdl_structure_l I (R := T') my.2.1) 6 :=
    ⟨Fin.cases a' (Fin.cases b' (Fin.cases r₁ (Fin.cases ℓ' (Fin.cases n' (fun _ => m'))))), fun _ => a'⟩
  have moved := smap_source_l I hZF hω mx my map
    (.conj (fn0_m (.bound 5) (.bound 4) (.bound 2))
      (cp0_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))
    (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]) ρ η
    (Fin.cases haa (Fin.cases hbb (Fin.cases hrR (Fin.cases hℓ (Fin.cases hnn (fun _ => hmm))))))
  simp only [Formula.satisfies_conj_iff, fn0_sat_l ex, fn0_sat_l ey, cp0_sat_l ex, cp0_sat_l ey] at moved
  have next := moved.mp ⟨fr, factor⟩
  have eq := ec_factor_unique_l ey inj next.1 fr' next.2 factor'
  exact ⟨hmm, hnn, (show R = r'.val from congrArg Subtype.val eq) ▸ hrR⟩

/-- 目标坐标过渡由原投影构造，并在两端实际对象码的像上严格交换。 -/
theorem Er_coord_d.copy_l
    {ω c N T c' N' T' σ z z' L L' a b a' b' i j D E t : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ) (ext : Rf_ext_d I N T)
    (w ξ ℓ : (smdl_structure_l I (R := T) mx.2.1).Domain)
    (w' ξ' ℓ' : (smdl_structure_l I (R := T') my.2.1).Domain)
    (hξ : Rd_entry_d ξ.val ξ'.val σ)
    (hℓ : Rd_entry_d ℓ.val ℓ'.val σ)
    (numbers : Rr_layer_d I ω N T w.val z) (numbers' : Rr_layer_d I ω N' T' w'.val z')
    (fa : Fn0_d i L a) (fa' : Fn0_d i L' a') (aa : Smap_assign_d I i σ a a')
    (fb : Fn0_d j L b) (fb' : Fn0_d j L' b') (bb : Smap_assign_d I j σ b b')
    (h : Er_coord_d I ω L N T ξ.val ℓ.val z a b D E t) :
    ∃ D' E' t', Er_coord_d I ω L' N' T' ξ'.val ℓ'.val z' a' b' D' E' t' ∧
      (∀ x x', Rd_entry_d x x' σ → (M.mem x D ↔ M.mem x' D')) ∧
      (∀ x x', Rd_entry_d x x' σ → (M.mem x E ↔ M.mem x' E')) ∧
      ∀ x y x' y', Rd_entry_d x x' σ → Rd_entry_d y y' σ →
        (Rd_entry_d x y t ↔ Rd_entry_d x' y' t') := by
  have ext' : Rf_ext_d I N' T' := map.extensional_l hZF hω mx my ext
  have ex := ext.native_l I mx.2.1
  have ey := ext'.native_l I my.2.1
  obtain ⟨u, v, d, e, p, cu, cv, native, dc, ec, _, graph⟩ := h.read_l I mx.2.1 ex ξ ℓ
  obtain ⟨u', hu', huu⟩ := map.1.1.2.2 u.val u.property
  obtain ⟨v', hv', hvv⟩ := map.1.1.2.2 v.val v.property
  obtain ⟨d', hd', hdd⟩ := map.1.1.2.2 d.val d.property
  obtain ⟨e', he', hee⟩ := map.1.1.2.2 e.val e.property
  obtain ⟨p', hp', hpp⟩ := map.1.1.2.2 p.val p.property
  let U : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨u', hu'⟩
  let V : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨v', hv'⟩
  let d₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨d', hd'⟩
  let e₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨e', he'⟩
  let P : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨p', hp'⟩
  let ρ : Env (smdl_structure_l I (R := T) mx.2.1) 7 :=
    ⟨Fin.cases p (Fin.cases e (Fin.cases d (Fin.cases v (Fin.cases u (Fin.cases ℓ (fun _ => ξ)))))), fun _ => p⟩
  let η : Env (smdl_structure_l I (R := T') my.2.1) 7 :=
    ⟨Fin.cases P (Fin.cases e₁ (Fin.cases d₁ (Fin.cases V (Fin.cases U (Fin.cases ℓ' (fun _ => ξ')))))), fun _ => P⟩
  have moved := smap_source_l I hZF hω mx my map
    (er_native_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) ρ η
    (Fin.cases hpp (Fin.cases hee (Fin.cases hdd (Fin.cases hvv (Fin.cases huu (Fin.cases hℓ (fun _ => hξ)))))))
  have next : Er_native_d ξ' ℓ' U V d₁ e₁ P :=
    (er_native_sat_l ey ..).mp (moved.mp ((er_native_sat_l ex ..).mpr native))
  have cu' := cu.image_l hZF hω mx my map ext numbers numbers' fa fa' aa huu
  have cv' := cv.image_l hZF hω mx my map ext numbers numbers' fb fb' bb hvv
  obtain ⟨m, n, r, fm, fn, fr, factor, ds, es, fp, ps⟩ := next
  obtain ⟨E', D', t', ec', dc', ft', graph'⟩ := smdl_graph_l hZF my.2.1 ey e₁ d₁ P fp
  refine ⟨D', E', t', Er_coord_d.of_native_l I my.2.1 ey ξ' ℓ' U V d₁ e₁ P cu' cv'
    ⟨m, n, r, fm, fn, fr, factor, ds, es, fp, ps⟩ dc' ec' ft' graph', ?_, ?_, ?_⟩
  · intro x x' hxx
    exact (dc x).trans ((and_iff_right (map.1.1.input_mem_of_pairMember hxx)).trans
      ((map.relation_l I hZF hω mx my hxx hdd).trans
        ((and_iff_right (map.1.1.output_mem_of_pairMember hxx)).symm.trans (dc' x').symm)))
  · intro x x' hxx
    exact (ec x).trans ((and_iff_right (map.1.1.input_mem_of_pairMember hxx)).trans
      ((map.relation_l I hZF hω mx my hxx hee).trans
        ((and_iff_right (map.1.1.output_mem_of_pairMember hxx)).symm.trans (ec' x').symm)))
  · intro x y x' y' hxx hyy
    let a₀ : (smdl_structure_l I (R := T) mx.2.1).Domain := ⟨x, map.1.1.input_mem_of_pairMember hxx⟩
    let b₀ : (smdl_structure_l I (R := T) mx.2.1).Domain := ⟨y, map.1.1.input_mem_of_pairMember hyy⟩
    let a₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨x', map.1.1.output_mem_of_pairMember hxx⟩
    let b₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨y', map.1.1.output_mem_of_pairMember hyy⟩
    let ρ₀ : Env (smdl_structure_l I (R := T) mx.2.1) 3 :=
      ⟨Fin.cases p (Fin.cases b₀ (fun _ => a₀)), fun _ => p⟩
    let ρ₁ : Env (smdl_structure_l I (R := T') my.2.1) 3 :=
      ⟨Fin.cases P (Fin.cases b₁ (fun _ => a₁)), fun _ => P⟩
    have values := smap_source_l I hZF hω mx my map (rd_entry0_m (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ρ₀ ρ₁
      (Fin.cases hpp (Fin.cases hyy (fun _ => hxx)))
    exact (graph a₀ b₀).trans ((rd_entry0_sat_l ex ..).symm.trans
      (values.trans ((rd_entry0_sat_l ey ..).trans (graph' a₁ b₁).symm)))

/-- 复制的支撑及投影接入目标实际过渡；任意代表仍使用同一个规范坐标图。 -/
theorem Er_graph_d.copy_coordinates_l
    {ω c N T c' N' T' σ z z' L L' X R Y S k k' F F'
      J O Z A p V W J' O' Z' A' p' V' W' a b a' b' i j D E t : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ) (ext : Rf_ext_d I N T)
    (w ξ ℓ : (smdl_structure_l I (R := T) mx.2.1).Domain)
    (w' ξ' ℓ' : (smdl_structure_l I (R := T') my.2.1).Domain)
    (hξ : Rd_entry_d ξ.val ξ'.val σ)
    (hℓ : Rd_entry_d ℓ.val ℓ'.val σ)
    (numbers : Rr_layer_d I ω N T w.val z) (numbers' : Rr_layer_d I ω N' T' w'.val z')
    (inside : M.MemberSubset L N) (inside' : M.MemberSubset L' N')
    (source : Er_graph_d I ω L N T ξ.val ℓ.val F z X R k J O Z A p V W)
    (target : Er_graph_d I ω L' N' T' ξ'.val ℓ'.val F' z' Y S k' J' O' Z' A' p' V' W')
    (fa : Fn0_d i L a) (fa' : Fn0_d i L' a') (aa : Smap_assign_d I i σ a a')
    (fb : Fn0_d j L b) (fb' : Fn0_d j L' b') (bb : Smap_assign_d I j σ b b')
    (ha' : M.mem a' J') (hb' : M.mem b' J') (edge : Rd_entry_d a b O)
    (coord : Er_coord_d I ω L N T ξ.val ℓ.val z a b D E t) :
    ∃ q o₀ C₀ W₀ o₁ C₁ W₁ D' E' t', Rd_entry_d a' b' O' ∧
      Rd_entry_d a' o₀ Z' ∧ Rd_entry_d b' o₁ Z' ∧ Smdl_d I o₀ C₀ W₀ ∧ Smdl_d I o₁ C₁ W₁ ∧
      Smap_d I ω o₀ o₁ C₀ C₁ q ∧
      (∀ B C, Rd_entry_d B C q ↔ M.mem B C₀ ∧ M.mem C C₁ ∧
        Er_arrow_d I ω L' N' T' ξ'.val ℓ'.val z' Y a' b' B C) ∧
      Er_coord_d I ω L' N' T' ξ'.val ℓ'.val z' a' b' D' E' t' ∧
      (∀ B C, Rd_entry_d B C q → ∀ g, M.mem g B → ∃ h, M.mem h C ∧ Cp0_d E' D' Y t' g h) ∧
      (∀ x x', Rd_entry_d x x' σ → (M.mem x D ↔ M.mem x' D')) ∧
      (∀ x x', Rd_entry_d x x' σ → (M.mem x E ↔ M.mem x' E')) ∧
      ∀ x y x' y', Rd_entry_d x x' σ → Rd_entry_d y y' σ →
        (Rd_entry_d x y t ↔ Rd_entry_d x' y' t') := by
  obtain ⟨_, _, r, m, n, hm, hn, fr, fn, factor⟩ := (source.order_spec a b).mp edge
  have eq := factor.1.domain_eq_l hZF.1 fa
  subst m
  have eq := fn.domain_eq_l hZF.1 fb
  subst n
  have factor' : Cp0_d i j L' r b' a' := ⟨fa', fun s hs => by
    obtain ⟨v, hv, x, hx, hsv, hvx, hsx⟩ := factor.2 s hs
    obtain ⟨x', _, hxx⟩ := map.1.1.2.2 x (inside x hx)
    have value := aa s hs x x' hsx hxx
    exact ⟨v, hv, x', (fa'.bound_l value).2, hsv, bb v hv x x' hvx hxx, value⟩⟩
  have edge' := (target.order_spec a' b').mpr ⟨ha', hb', r, i, j, hm, hn, fr, fb', factor'⟩
  obtain ⟨D₁, E₁, t₁, copied, cd, ce, ct⟩ :=
    coord.copy_l hZF hω mx my map ext w ξ ℓ w' ξ' ℓ' hξ hℓ numbers numbers' fa fa' aa fb fb' bb
  obtain ⟨q, o₀, C₀, W₀, o₁, C₁, W₁, first, last, m₀, m₁, embed, spec, D', E', t', next, any⟩ :=
    target.transition a' b' edge'
  obtain ⟨_, _, _, inj⟩ := (target.indices b').mp hb'
  have ext' : Rf_ext_d I N' T' := map.extensional_l hZF hω mx my ext
  obtain ⟨rfl, rfl, rfl⟩ := copied.unique_l hZF numbers' (ext'.native_l I _) ξ' ℓ' inside' inj next
  exact ⟨q, o₀, C₀, W₀, o₁, C₁, W₁, D₁, E₁, t₁, edge', first, last, m₀, m₁, embed, spec,
    next, any, cd, ce, ct⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际重排下原代表复制与投影交换

共同部分只需原有有限幂子集一致性。重排函数以单点子集得到共同像；
拉回方程只以这个函数图为参数，经完整初等性覆盖目标的全部新坐标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原投影公式沿共同图读取为父模型中的函数图复合。 -/
theorem er_reindex_read_l {ω N T X R Γ k z D E u v t R₀ : M.Domain}
    (nx : ∃ x, M.mem x N) (px : ∃ x, M.mem x X)
    (ex : Extensional (smdl_structure_l I (R := T) nx))
    (ep : Extensional (smdl_structure_l I (R := R) px))
    (ξ m n r d e : (smdl_structure_l I (R := T) nx).Domain)
    (agree : Er_agree_d I ω N T ξ.val z Γ X R k)
    (hm : (smdl_structure_l I (R := T) nx).mem m ξ)
    (hn : (smdl_structure_l I (R := T) nx).mem n ξ)
    (hr : Rd_entry_d r.val R₀ k) (fr : Fn0_d m n r) (es : Ep_space_d ξ n e)
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T)
    (ec : ∀ x, M.mem x E ↔ M.mem x N ∧ Rd_entry_d x e.val T)
    (fu : Fn0_d D X u) (fv : Fn0_d E X v)
    (ru : M.IsRestrictionOf I u k D) (rv : M.IsRestrictionOf I v k E)
    (projection : ∀ s q : (smdl_structure_l I (R := T) nx).Domain,
      Rd_entry_d s.val q.val t ↔ (smdl_structure_l I (R := T) nx).mem s e ∧ Cp0_d m n ξ r s q) :
    ∀ s q x y, Rd_entry_d s x v → Rd_entry_d q y u →
      (Rd_entry_d s q t ↔ Rf_comp_d I X R R₀ x y) := by
  obtain ⟨M₀, hM, hmM⟩ := agree.injection.1.2.2 m.val (agree.downward ξ.val m.val agree.critical m.property hm)
  obtain ⟨N₀, hN, hnN⟩ := agree.injection.1.2.2 n.val (agree.downward ξ.val n.val agree.critical n.property hn)
  obtain ⟨K₀, hK, hξK⟩ := agree.injection.1.2.2 ξ.val agree.critical
  let m₁ : (smdl_structure_l I (R := R) px).Domain := ⟨M₀, hM⟩
  let n₁ : (smdl_structure_l I (R := R) px).Domain := ⟨N₀, hN⟩
  let ξ₁ : (smdl_structure_l I (R := R) px).Domain := ⟨K₀, hK⟩
  let r₁ : (smdl_structure_l I (R := R) px).Domain := ⟨R₀, agree.injection.1.output_mem_of_pairMember hr⟩
  intro s q x y hsx hqy
  let s₀ : (smdl_structure_l I (R := T) nx).Domain := ⟨s, ((ec s).mp (fv.bound_l hsx).1).1⟩
  let q₀ : (smdl_structure_l I (R := T) nx).Domain := ⟨q, ((dc q).mp (fu.bound_l hqy).1).1⟩
  let x₁ : (smdl_structure_l I (R := R) px).Domain := ⟨x, (fv.bound_l hsx).2⟩
  let y₁ : (smdl_structure_l I (R := R) px).Domain := ⟨y, (fu.bound_l hqy).2⟩
  have hse := ((ec s).mp (fv.bound_l hsx).1).2
  have comp := rr_graph_comp_l I nx px ex ep agree.domain agree.downward agree.injection agree.predecessors
    m n ξ r s₀ q₀ m₁ n₁ ξ₁ r₁ x₁ y₁ hmM hnN hξK hr ((rv.2 s x).mp hsx).2 ((ru.2 q y).mp hqy).2
    fr ((es s₀).mp hse)
  exact (projection s₀ q₀).trans ((and_iff_right hse).trans
    (comp.symm.trans (rf_comp_native_l I px ep r₁ x₁ y₁).symm))

/-- 两端实际有限幂、重排和代表给出复制与拉回的交换；不假设商上的交换方块。 -/
private theorem er_copy_pull_l
    {ω c N T c' N' T' σ h X R h' Y S π Γ Γ' k k' z z' a b
      D E D' E' u v u' v' t t' d₀ e₀ d₁ e₁ g h₀ g' h₁ : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ) (ext : Rf_ext_d I N T)
    (ξ m n r d e ℓ f₀ f₁ : (smdl_structure_l I (R := T) mx.2.1).Domain)
    (ξ' m' n' r' d' e' ℓ' f₀' f₁' : (smdl_structure_l I (R := T') my.2.1).Domain)
    (single : ∃ p, Pair_d (smdl_structure_l I (R := T) mx.2.1) p r r)
    (hξ : Rd_entry_d ξ.val ξ'.val σ) (hℓ : Rd_entry_d ℓ.val ℓ'.val σ)
    (hf₀ : Rd_entry_d f₀.val f₀'.val σ) (hf₁ : Rd_entry_d f₁.val f₁'.val σ)
    (hm : (smdl_structure_l I (R := T) mx.2.1).mem m ξ)
    (hn : (smdl_structure_l I (R := T) mx.2.1).mem n ξ)
    (sub : (smdl_structure_l I (R := T) mx.2.1).MemberSubset n ξ)
    (ha : M.mem a ω) (hb : M.mem b ω) (ham : Rd_entry_d a m.val z) (hbn : Rd_entry_d b n.val z)
    (fa : Fn0_d m ℓ f₀) (fb : Fn0_d n ℓ f₁) (fr : Fn0_d m n r) (factor : Cp0_d m n ℓ r f₁ f₀)
    (fa' : Fn0_d m' ℓ' f₀') (fb' : Fn0_d n' ℓ' f₁') (fr' : Fn0_d m' n' r') (factor' : Cp0_d m' n' ℓ' r' f₁' f₀')
    (inj : ∀ i j x, Rd_entry_d i x f₁' → Rd_entry_d j x f₁' → i = j)
    (ds : Ep_space_d ξ m d) (es : Ep_space_d ξ n e)
    (ds' : Ep_space_d ξ' m' d') (es' : Ep_space_d ξ' n' e')
    (parent : Smdl_d I h X R) (parent' : Smdl_d I h' Y S)
    (copy : Smap_d I ω h h' X Y π) (px : Rf_ext_d I X R)
    (agree : Er_agree_d I ω N T ξ.val z Γ X R k)
    (agree' : Er_agree_d I ω N' T' ξ'.val z' Γ' Y S k')
    (maps : Er_maps_d I ω N T ξ.val z k k' π σ)
    (hd₀ : Rd_entry_d d.val d₀ k) (he₀ : Rd_entry_d e.val e₀ k)
    (hd₁ : Rd_entry_d d'.val d₁ k') (he₁ : Rd_entry_d e'.val e₁ k')
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T)
    (ec : ∀ x, M.mem x E ↔ M.mem x N ∧ Rd_entry_d x e.val T)
    (dc' : ∀ x, M.mem x D' ↔ M.mem x N' ∧ Rd_entry_d x d'.val T')
    (ec' : ∀ x, M.mem x E' ↔ M.mem x N' ∧ Rd_entry_d x e'.val T')
    (fu : Fn0_d D X u) (fv : Fn0_d E X v) (ft : Fn0_d E D t)
    (fu' : Fn0_d D' Y u') (fv' : Fn0_d E' Y v') (ft' : Fn0_d E' D' t')
    (ru : M.IsRestrictionOf I u k D) (rv : M.IsRestrictionOf I v k E)
    (ru' : M.IsRestrictionOf I u' k' D') (rv' : M.IsRestrictionOf I v' k' E')
    (proj : ∀ s q : (smdl_structure_l I (R := T) mx.2.1).Domain,
      Rd_entry_d s.val q.val t ↔ (smdl_structure_l I (R := T) mx.2.1).mem s e ∧ Cp0_d m n ξ r s q)
    (proj' : ∀ s q : (smdl_structure_l I (R := T') my.2.1).Domain,
      Rd_entry_d s.val q.val t' ↔ (smdl_structure_l I (R := T') my.2.1).mem s e' ∧ Cp0_d m' n' ξ' r' s q)
    (fg : Fn0_d D X g) (fg' : Fn0_d D' Y g') (fh' : Fn0_d E' Y h₁)
    (cg : Rc_copy_d I X R d₀ u Y S u' π g g') (ch : Rc_copy_d I X R e₀ v Y S v' π h₀ h₁)
    (pull : Cp0_d E D X t g h₀) : Cp0_d E' D' Y t' g' h₁ := by
  have ext' : Rf_ext_d I N' T' := map.extensional_l hZF hω mx my ext
  have py : Rf_ext_d I Y S := copy.extensional_l hZF hω parent parent' px
  have ex := ext.native_l I mx.2.1
  have ey := ext'.native_l I my.2.1
  obtain ⟨hmm, hnn, hrr⟩ := er_factor_image_l hZF hω mx my map ext m n ℓ f₀ f₁ r m' n' ℓ' f₀' f₁' r'
    hℓ hf₀ hf₁ fa fb fr factor fa' fb' fr' factor' inj
  have space := (er_space_native_l I mx.2.1 ex ξ m d).mpr ds
  have spaceE := (er_space_native_l I mx.2.1 ex ξ n e).mpr es
  have hdd := space.image_unique_l I hZF hω mx my map ey hξ hmm ((er_space_native_l I my.2.1 ey ξ' m' d').mpr ds')
  have hee := spaceE.image_unique_l I hZF hω mx my map ey hξ hnn ((er_space_native_l I my.2.1 ey ξ' n' e').mpr es')
  -- 有限幂对象自身是其子集，故两端父模型的定义域像被唯一确定。
  obtain ⟨d₂, _, hd₂⟩ := copy.1.1.2.2 d₀ (agree.injection.1.output_mem_of_pairMember hd₀)
  obtain ⟨e₂, _, he₂⟩ := copy.1.1.2.2 e₀ (agree.injection.1.output_mem_of_pairMember he₀)
  have hd' := maps a m.val d.val d.val d'.val d₀ d₂ ha ham space d.property (fun _ _ h => h) hd₀ hdd hd₂
  have he' := maps b n.val e.val e.val e'.val e₀ e₂ hb hbn spaceE e.property (fun _ _ h => h) he₀ hee he₂
  have hd : Rd_entry_d d₀ d₁ π := agree'.injection.1.1.2 d'.val d₂ d₁ hd' hd₁ ▸ hd₂
  have he : Rd_entry_d e₀ e₁ π := agree'.injection.1.1.2 e'.val e₂ e₁ he' he₁ ▸ he₂
  -- 只对实际重排函数使用单点子集；不要求整个投影图属于有限幂。
  have hrd := (ds r).mpr (fr.mono_target_l sub)
  obtain ⟨R₀, hR, hrR⟩ := agree.injection.1.2.2 r.val
    (agree.downward d.val r.val (agree.injection.1.input_mem_of_pairMember hd₀) r.property hrd)
  obtain ⟨R₁, _, hRR⟩ := copy.1.1.2.2 R₀ hR
  have hrR' := maps.point_l hZF hω mx my map ext parent parent' copy px agree agree'
    ha ham space r.property single hrd hrR hrr hRR
  have read := er_reindex_read_l hZF mx.2.1 parent.2.1 ex (px.native_l I parent.2.1)
    ξ m n r d e agree hm hn hrR fr es dc ec fu fv ru rv proj
  have read' := er_reindex_read_l hZF my.2.1 parent'.2.1 ey (py.native_l I parent'.2.1)
    ξ' m' n' r' d' e' agree' ((map.relation_l I hZF hω mx my hmm hξ).mp hm)
    ((map.relation_l I hZF hω mx my hnn hξ).mp hn) hrR' fr' es' dc' ec' fu' fv' ru' rv' proj'
  have ontoD x (hx : Rd_entry_d x d₀ R) : ∃ s, Rd_entry_d s x u := by
    obtain ⟨s, hsd, hsx⟩ := (agree.predecessors d.val d₀ hd₀ x).mp hx
    exact ⟨s, (ru.2 s x).mpr ⟨(dc s).mpr ⟨agree.domain s (agree.injection.1.input_mem_of_pairMember hsx), hsd⟩, hsx⟩⟩
  have ontoE x (hx : Rd_entry_d x e₀ R) : ∃ s, Rd_entry_d s x v := by
    obtain ⟨s, hse, hsx⟩ := (agree.predecessors e.val e₀ he₀ x).mp hx
    exact ⟨s, (rv.2 s x).mpr ⟨(ec s).mpr ⟨agree.domain s (agree.injection.1.input_mem_of_pairMember hsx), hse⟩, hsx⟩⟩
  have domD s x (hsx : Rd_entry_d s x u') := (agree'.predecessors d'.val d₁ hd₁ x).mpr
    ⟨s, ((dc' s).mp (fu'.bound_l hsx).1).2, ((ru'.2 s x).mp hsx).2⟩
  have domE s x (hsx : Rd_entry_d s x v') := (agree'.predecessors e'.val e₁ he₁ x).mpr
    ⟨s, ((ec' s).mp (fv'.bound_l hsx).1).2, ((rv'.2 s x).mp hsx).2⟩
  exact rc_copy_pull_l hZF hω parent parent' copy px hd he hRR ft fu' fv' ft' fg fg' fh'
    ontoD ontoE domD domE read (fun s q x y hsq hsx hqy => (read' s q x y hsx hqy).mp hsq) cg ch pull

/-- 实际两端坐标和支撑逐点像自动给出代表拉回的复制相容性。 -/
theorem Er_coord_d.copy_pull_l
    {ω c N T c' N' T' σ h X R h' Y S π Γ Γ' k k' z z' L L' a b a' b' i j
      D E D' E' u v u' v' t t' d₀ e₀ d₁ e₁ g h₀ g' h₁ : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ) (ext : Rf_ext_d I N T)
    (w ξ ℓ d e : (smdl_structure_l I (R := T) mx.2.1).Domain)
    (w' ξ' ℓ' d' e' : (smdl_structure_l I (R := T') my.2.1).Domain)
    (single : ∀ r : (smdl_structure_l I (R := T) mx.2.1).Domain, ∃ p,
      Pair_d (smdl_structure_l I (R := T) mx.2.1) p r r)
    (trans : (smdl_structure_l I (R := T) mx.2.1).TransitiveSet ξ)
    (hwξ : (smdl_structure_l I (R := T) mx.2.1).mem w ξ)
    (hξ : Rd_entry_d ξ.val ξ'.val σ) (hℓ : Rd_entry_d ℓ.val ℓ'.val σ)
    (numbers : Rr_layer_d I ω N T w.val z) (numbers' : Rr_layer_d I ω N' T' w'.val z')
    (fa : Fn0_d i L a) (fa' : Fn0_d i L' a') (aa : Smap_assign_d I i σ a a')
    (fb : Fn0_d j L b) (fb' : Fn0_d j L' b') (bb : Smap_assign_d I j σ b b')
    (inside' : M.MemberSubset L' N') (inj : ∀ x y v, Rd_entry_d x v b' → Rd_entry_d y v b' → x = y)
    (parent : Smdl_d I h X R) (parent' : Smdl_d I h' Y S)
    (copy : Smap_d I ω h h' X Y π) (px : Rf_ext_d I X R)
    (agree : Er_agree_d I ω N T ξ.val z Γ X R k)
    (agree' : Er_agree_d I ω N' T' ξ'.val z' Γ' Y S k')
    (maps : Er_maps_d I ω N T ξ.val z k k' π σ)
    (hd₀ : Rd_entry_d d.val d₀ k) (he₀ : Rd_entry_d e.val e₀ k)
    (hd₁ : Rd_entry_d d'.val d₁ k') (he₁ : Rd_entry_d e'.val e₁ k')
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T)
    (ec : ∀ x, M.mem x E ↔ M.mem x N ∧ Rd_entry_d x e.val T)
    (dc' : ∀ x, M.mem x D' ↔ M.mem x N' ∧ Rd_entry_d x d'.val T')
    (ec' : ∀ x, M.mem x E' ↔ M.mem x N' ∧ Rd_entry_d x e'.val T')
    (fu : Fn0_d D X u) (fv : Fn0_d E X v) (fu' : Fn0_d D' Y u') (fv' : Fn0_d E' Y v')
    (ru : M.IsRestrictionOf I u k D) (rv : M.IsRestrictionOf I v k E)
    (ru' : M.IsRestrictionOf I u' k' D') (rv' : M.IsRestrictionOf I v' k' E')
    (coord : Er_coord_d I ω L N T ξ.val ℓ.val z a b D E t)
    (coord' : Er_coord_d I ω L' N' T' ξ'.val ℓ'.val z' a' b' D' E' t')
    (fg : Fn0_d D X g) (fg' : Fn0_d D' Y g') (fh' : Fn0_d E' Y h₁)
    (cg : Rc_copy_d I X R d₀ u Y S u' π g g') (ch : Rc_copy_d I X R e₀ v Y S v' π h₀ h₁)
    (pull : Cp0_d E D X t g h₀) : Cp0_d E' D' Y t' g' h₁ := by
  have ext' : Rf_ext_d I N' T' := map.extensional_l hZF hω mx my ext
  have ex := ext.native_l I mx.2.1
  have ey := ext'.native_l I my.2.1
  obtain ⟨f₀, f₁, d₂, e₂, p, ca, cb, native, dc₂, ec₂, ft, gp⟩ := coord.read_l I mx.2.1 ex ξ ℓ
  obtain ⟨f₀', f₁', d₂', e₂', p', ca', cb', native', dc₂', ec₂', ft', gp'⟩ := coord'.read_l I my.2.1 ey ξ' ℓ'
  -- 相同的完整对象码载体唯一确定原有限幂，不要求先指定原对象的对应。
  have eqd : d₂ = d := ex.eq_of_same_members d₂ d (fun x =>
    ⟨fun h => ((dc x.val).mp ((dc₂ x.val).mpr ⟨x.property, h⟩)).2,
      fun h => ((dc₂ x.val).mp ((dc x.val).mpr ⟨x.property, h⟩)).2⟩)
  have eqe : e₂ = e := ex.eq_of_same_members e₂ e (fun x =>
    ⟨fun h => ((ec x.val).mp ((ec₂ x.val).mpr ⟨x.property, h⟩)).2,
      fun h => ((ec₂ x.val).mp ((ec x.val).mpr ⟨x.property, h⟩)).2⟩)
  have eqd' : d₂' = d' := ey.eq_of_same_members d₂' d' (fun x =>
    ⟨fun h => ((dc' x.val).mp ((dc₂' x.val).mpr ⟨x.property, h⟩)).2,
      fun h => ((dc₂' x.val).mp ((dc' x.val).mpr ⟨x.property, h⟩)).2⟩)
  have eqe' : e₂' = e' := ey.eq_of_same_members e₂' e' (fun x =>
    ⟨fun h => ((ec' x.val).mp ((ec₂' x.val).mpr ⟨x.property, h⟩)).2,
      fun h => ((ec₂' x.val).mp ((ec' x.val).mpr ⟨x.property, h⟩)).2⟩)
  subst d₂ e₂ d₂' e₂'
  obtain ⟨m, n, r, f₀n, f₁n, fr, factor, ds, es, _, ps⟩ := native
  obtain ⟨m', n', r', f₀n', f₁n', fr', factor', ds', es', _, ps'⟩ := native'
  have hf₀ := ca.map_l hZF hω mx my map ext numbers numbers' fa fa' aa ca'
  have hf₁ := cb.map_l hZF hω mx my map ext numbers numbers' fb fb' bb cb'
  have hm := ca.domain_l I hZF.1 mx.2.1 ex m ℓ f₀ fa f₀n
  have hn := cb.domain_l I hZF.1 mx.2.1 ex n ℓ f₁ fb f₁n
  have hn' := cb'.domain_l I hZF.1 my.2.1 ey n' ℓ' f₁' fb' f₁n'
  have graph' := cb'.elim fun _ h => h.elim fun _ h => h.2.2.2.2
  have inj' := (numbers'.function_injective_l hZF ey n' ℓ' f₁' hn'.2 f₁n' (fb'.mono_target_l inside') graph').mp inj
  have hmξ := trans w hwξ m ((numbers.image m.val).mpr ⟨i, hm.1, hm.2⟩)
  have hnξ := trans w hwξ n ((numbers.image n.val).mpr ⟨j, hn.1, hn.2⟩)
  exact er_copy_pull_l hZF hω mx my map ext ξ m n r d e ℓ f₀ f₁ ξ' m' n' r' d' e' ℓ' f₀' f₁'
    (single r) hξ hℓ hf₀ hf₁ hmξ hnξ (trans n hnξ) hm.1 hn.1 hm.2 hn.2
    f₀n f₁n fr factor f₀n' f₁n' fr' factor' inj' ds es ds' es'
    parent parent' copy px agree agree' maps hd₀ he₀ hd₁ he₁ dc ec dc' ec' fu fv ft fu' fv' ft' ru rv ru' rv'
    (fun s q => (gp s q).trans (ps s q)) (fun s q => (gp' s q).trans (ps' s q)) fg fg' fh' cg ch pull

end YesMetaZFC.SetTheory.LargeCardinal
