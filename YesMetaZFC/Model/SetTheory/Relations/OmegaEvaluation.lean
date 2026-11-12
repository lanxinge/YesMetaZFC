import YesMetaZFC.Model.SetTheory.Relations.Collection
import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Source.OmegaClosed
import YesMetaZFC.SetTheory.CountableChoice
import YesMetaZFC.SetTheory.Notation

/-! # 原关系中固定定义域上的公式统一化

有限参数编入同一实际赋值，两个实参由更新图读取；原统一化证书
随后给出关系模型自身的函数对象。模型内部不另加任何公理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem Sc_uniform_d.formula_l {ω X R : M.Domain} (hω : M.IsOmega ω) (nx : ∃ x, M.mem x X)
    (D : (smdl_structure_l I (R := R) nx).Domain) (uniform : Sc_uniform_d I ω X R D.val)
    {p} (φ : BinarySchema p) (ρ : Env (smdl_structure_l I (R := R) nx) p)
    (total : ∀ x, (smdl_structure_l I (R := R) nx).mem x D → ∃ y, φ.denote ρ x y) :
    ∃ F B : (smdl_structure_l I (R := R) nx).Domain, Fn0_d D B F ∧
      ∀ x y, Rd_entry_d x y F → φ.denote ρ x y := by
  obtain ⟨z, n, G, r, v, program, hv, compile⟩ := source_compile_l I hZF hω φ.body φ.freeClosed
  have hi k := num_mem_l hZF.1 hω (hv k)
  have inj : Function.Injective v := fun i j h => Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) (h.symm ▸ hv j))
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨a, ha, params⟩ := senv_params_l I hZF hE nx v
    (fun k => (((ρ.push D).push D).bound k).val) inj hi (fun k => (((ρ.push D).push D).bound k).property)
  have ne : v (Fin.succ 0) ≠ v 0 := fun h => Fin.succ_ne_zero 0 (inj h)
  -- 输入与输出占两个不同编号；其余有限参数在两次更新下保持。
  have read (x y : (smdl_structure_l I (R := R) nx).Domain) :
      Sbin_d I X R E G n r (v (Fin.succ 0)) (v 0) a x.val y.val ↔ φ.denote ρ x y := by
    obtain ⟨b, bx, hb⟩ := senv_update_exists_l I hZF ((hE a).mp ha) (hi (Fin.succ 0)) x.property
    obtain ⟨c, cy, hc⟩ := senv_update_exists_l I hZF hb (hi 0) y.property
    apply (sbin_value_l I hZF.1 bx cy).trans
    apply compile X R nx E hE c ((hE c).mpr hc) ((ρ.push x).push y)
    refine Fin.cases ((cy.2 (v 0) y.val).mpr (Or.inl ⟨rfl, rfl⟩)) (Fin.cases ?_ ?_)
    · exact (cy.2 (v (Fin.succ 0)) x.val).mpr (Or.inr ⟨ne, (bx.2 (v (Fin.succ 0)) x.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩)
    · intro k
      have n₀ : v k.succ.succ ≠ v 0 := fun h => Fin.succ_ne_zero k.succ (inj h)
      have n₁ : v k.succ.succ ≠ v (Fin.succ 0) := by
        intro h
        have eq := congrArg Fin.val (inj h)
        simp only [Fin.val_succ, Fin.val_zero] at eq
        omega
      exact (cy.2 (v k.succ.succ) (ρ.bound k).val).mpr (Or.inr ⟨n₀,
        (bx.2 (v k.succ.succ) (ρ.bound k).val).mpr (Or.inr ⟨n₁, params k.succ.succ⟩)⟩)
  obtain ⟨F, B, fn, select⟩ := uniform.raw_l I nx D hE program.2.1 program.2.2
    (hi (Fin.succ 0)) (hi 0) ne ha (fun x hx => (total x hx).imp fun y hy => (read x y).mpr hy)
  exact ⟨F, B, fn, fun x y hxy => (read x y).mp (select x y hxy)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 由实际函数与支撑求值回收整个目标的可数列

DC 在既有表示中选择两列。源闭性回收函数码列，共同层闭性回收支撑像列；
同一初等图搬运函数列，目标在其自然数定义域上统一逐点求值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Sc_omega_closed_d.evaluation_l {ω c X R d Y S j B u H w₀ w₁ z₀ z₁ : M.Domain}
    (hω : M.IsOmega ω) (hDC : Dc_d I ω)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (map : Smap_d I ω c d X Y j)
    (ext : Rf_ext_d I X R) (old : Rr_layer_d I ω X R w₀ z₀) (next : Rr_layer_d I ω Y S w₁ z₁)
    (hw : Rd_entry_d w₀ w₁ j)
    (numeric : ∀ n x, Rd_entry_d n x z₀ → ∀ y, Rd_entry_d n y z₁ ↔ Rd_entry_d x y j)
    (uniform : Sc_uniform_d I ω Y S w₁) (fu : M.IsSetFunctionFromTo I u B Y)
    (inside : ∀ b a, Rd_entry_d b a u → Rd_entry_d a H S)
    (cover : ∀ E, M.mem E Y → ∃ b d f a F, M.mem b B ∧ Rf_fun_d I X R d f ∧
      Rd_entry_d b a u ∧ Rd_entry_d f F j ∧ Rf_val_d I Y S a E F)
    (capture : ∀ a, Fn0_d ω Y a → (∀ n x, Rd_entry_d n x a → Rd_entry_d x H S) →
      ∃ A, Rf_fun_d I Y S w₁ A ∧ Rc_graph_d I Y S z₁ A a)
    (closed : Sc_omega_closed_d I ω X R) : Sc_omega_closed_d I ω Y S := by
  have ey : Rf_ext_d I Y S := map.extensional_l hZF hω mx my ext
  have en := ey.native_l I my.2.1
  refine ⟨w₁, z₁, next, fun s fs => ?_⟩
  -- 两次 DC 选择始终约束同一个原目标值和同一个原函数码。
  -- 参数依次为目标列、支撑域、支撑图、原初等图及两侧载体与关系。
  let ρ : Env M 8 := ⟨Fin.cases s (Fin.cases B (Fin.cases u (Fin.cases j
    (Fin.cases X (Fin.cases R (Fin.cases Y (fun _ => S))))))), fun _ => s⟩
  let v : Fin 10 → Term 10 := Term.bound
  let φ : BinarySchema 8 := {
    body := set[10] ⟪∃ E d b a F,
    ⌜rd_entry0_m⌝ₚ(⌜(v 1)⌝ₛ, E, ⌜(v 2)⌝ₛ) ∧ b ∈ ⌜(v 3)⌝ₛ ∧
    ⌜(rf_fun_m (𝒞 := kpair_convention_l))⌝ₚ(⌜(v 6)⌝ₛ, ⌜(v 7)⌝ₛ, d, ⌜(v 0)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(b, a, ⌜(v 4)⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜(v 0)⌝ₛ, F, ⌜(v 5)⌝ₛ) ∧
    ⌜(rf_val_m (𝒞 := kpair_convention_l))⌝ₚ(⌜(v 8)⌝ₛ, ⌜(v 9)⌝ₛ, a, E, F)⟫
    freeClosed := by simp -implicitDefEqProofs [v, Definitional.Formula.FreeClosed] }
  have read n f : φ.denote ρ n f ↔ ∃ E d b a F, Rd_entry_d n E s ∧ M.mem b B ∧
      Rf_fun_d I X R d f ∧ Rd_entry_d b a u ∧ Rd_entry_d f F j ∧ Rf_val_d I Y S a E F := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1, rf_fun_sat_l I, rf_val_sat_l I,
      Definitional.Term.eval_weaken]; rfl
  obtain ⟨G, fG, select⟩ := dc_uniformize_formula_l hZF φ ρ hω hDC (X := X) (fun n hn => by
    obtain ⟨E, hE, hnE⟩ := fs.2.1 n hn
    obtain ⟨b, d, f, a, F, hb, ff, hba, hfF, val⟩ := cover E hE
    exact ⟨f, ff.mem_l I, (read n f).mpr ⟨E, d, b, a, F, hnE, hb, ff, hba, hfF, val⟩⟩)
  let v : Fin 11 → Term 11 := Term.bound
  let ψ : BinarySchema 9 := {
    body := set[11] ⟪∃ E f d a F,
    ⌜rd_entry0_m⌝ₚ(⌜(v 1)⌝ₛ, E, ⌜(v 3)⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜(v 1)⌝ₛ, f, ⌜(v 2)⌝ₛ) ∧
    ⌜(rf_fun_m (𝒞 := kpair_convention_l))⌝ₚ(⌜(v 7)⌝ₛ, ⌜(v 8)⌝ₛ, d, f) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(v 0)⌝ₛ, a, ⌜(v 5)⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(f, F, ⌜(v 6)⌝ₛ) ∧
    ⌜(rf_val_m (𝒞 := kpair_convention_l))⌝ₚ(⌜(v 9)⌝ₛ, ⌜(v 10)⌝ₛ, a, E, F)⟫
    freeClosed := by simp -implicitDefEqProofs [v, Definitional.Formula.FreeClosed] }
  have row n b : ψ.denote (ρ.push G) n b ↔ ∃ E f d a F, Rd_entry_d n E s ∧ Rd_entry_d n f G ∧
      Rf_fun_d I X R d f ∧ Rd_entry_d b a u ∧ Rd_entry_d f F j ∧ Rf_val_d I Y S a E F := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, rf_fun_sat_l I, rf_val_sat_l I, Definitional.Term.eval_weaken]; rfl
  obtain ⟨b, fb, rows⟩ := dc_uniformize_formula_l hZF ψ (ρ.push G) hω hDC (X := B) (fun n hn => by
    obtain ⟨f, _, hnf⟩ := fG.2.1 n hn
    obtain ⟨E, d, b, a, F, hnE, hb, ff, hba, hfF, val⟩ := (read n f).mp (select n f hnf)
    exact ⟨b, hb, (row n b).mpr ⟨E, f, d, a, F, hnE, hnf, ff, hba, hfF, val⟩⟩)
  obtain ⟨a, fa, comp⟩ := ZF.exists_compositionFunction hZF I (fn0_function_l (ZF.modelsKP hZF) fb) fu
  obtain ⟨A, fA, gA⟩ := capture a (fn0_of_function_l (ZF.modelsKP hZF) fa) (fun n x hnx => by
    obtain ⟨_, b, _, hbx⟩ := (comp n x).mp hnx
    exact inside b x hbx)
  obtain ⟨G₀, fg₀, gg₀⟩ := closed.at_l I (ZF.modelsKP hZF) hω ext old G fG
  obtain ⟨G₁, hG₁, hG⟩ := map.1.1.2.2 G₀ (fg₀.mem_l I)
  have fg₁ := fg₀.map_l I hZF hω mx my map hw hG
  have evaluate n (hn : M.mem n ω) x (hnx : Rd_entry_d n x z₁) :
      ∃ a F E d, Rf_val_d I Y S x a A ∧ Rf_val_d I Y S x F G₁ ∧ Rd_entry_d n E s ∧
        Rf_fun_d I Y S d F ∧ Rf_val_d I Y S a E F := by
    obtain ⟨b₀, _, hnb⟩ := fb.2.1 n hn
    obtain ⟨E, f, d, a₀, F, hnE, hnf, ff, hba, hfF, value⟩ := (row n b₀).mp (rows n b₀ hnb)
    obtain ⟨x₀, _, hnx₀⟩ := old.injection.1.2.2 n hn
    have hx := (numeric n x₀ hnx₀ x).mp hnx
    have point := ((gg₀ n x₀ f hnx₀).mp hnf).map_l I hZF hω mx my map hx hfF hG
    obtain ⟨d', _, hdd⟩ := map.1.1.2.2 d (ff.elim fun hd _ => hd)
    exact ⟨a₀, F, E, d', (gA n x a₀ hnx).mp ((comp n a₀).mpr ⟨hn, b₀, hnb, hba⟩), point, hnE,
      ff.map_l I hZF hω mx my map hdd hfF, value⟩
  -- 原关系内部对 A(x) 与 j(G)(x) 求值，统一见证仍是目标自身的函数对象。
  let N := smdl_structure_l I (R := S) my.2.1
  let w : N.Domain := ⟨w₁, next.member⟩
  let A₀ : N.Domain := ⟨A, fA.mem_l I⟩
  let G' : N.Domain := ⟨G₁, hG₁⟩
  let ε : Env N 2 := ⟨Fin.cases A₀ (fun _ => G'), fun _ => w⟩
  let v : Fin 4 → Term 4 := Term.bound
  let χ : BinarySchema 2 := {
    body := set[4] ⟪∃ a f,
    ⌜rd_entry0_m⌝ₚ(⌜(v 1)⌝ₛ, a, ⌜(v 2)⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜(v 1)⌝ₛ, f, ⌜(v 3)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(a, ⌜(v 0)⌝ₛ, f)⟫
    freeClosed := by simp -implicitDefEqProofs [v, Definitional.Formula.FreeClosed] }
  have sat (x y : N.Domain) : χ.denote ε x y ↔ ∃ a f : N.Domain,
      Rd_entry_d x a A₀ ∧ Rd_entry_d x f G' ∧ Rd_entry_d a y f := by
    simp only [χ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l en, Definitional.Term.eval_weaken]; rfl
  have total (x : N.Domain) (hx : N.mem x w) : ∃ y : N.Domain, χ.denote ε x y := by
    obtain ⟨n, hn, hnx⟩ := (next.image x.val).mp hx
    obtain ⟨a, F, E, _, xa, xF, hnE, _, value⟩ := evaluate n hn x.val hnx
    let a' : N.Domain := ⟨a, (xa.bounds_l I).2.1⟩
    let f' : N.Domain := ⟨F, (xF.bounds_l I).2.1⟩
    let y : N.Domain := ⟨E, (fs.bound_l hnE).2⟩
    exact ⟨y, (sat x y).mpr ⟨a', f', (rf_val_native_l I my.2.1 en x a' A₀).mp xa,
      (rf_val_native_l I my.2.1 en x f' G').mp xF, (rf_val_native_l I my.2.1 en a' y f').mp value⟩⟩
  obtain ⟨T, Q, fn, choose⟩ := uniform.formula_l I hZF hω my.2.1 w χ ε total
  have fT := (rf_fun_native_l I my.2.1 en w T).mpr ⟨Q, fn⟩
  refine ⟨T.val, fT, fun n x E hnx => ?_⟩
  have hn := next.injection.1.input_mem_of_pairMember hnx
  have hx := next.injection.1.output_mem_of_pairMember hnx
  have hxw := (next.image x).mpr ⟨n, hn, hnx⟩
  obtain ⟨a₀, F, E₀, d₀, xa, xF, hnE, ff, value⟩ := evaluate n hn x hnx
  have selected y (hxy : Rf_val_d I Y S x y T.val) : y = E₀ := by
    let x' : N.Domain := ⟨x, hx⟩
    let y' : N.Domain := ⟨y, (hxy.bounds_l I).2.1⟩
    obtain ⟨a', f', ha, hf, val⟩ := (sat x' y').mp (choose x' y' ((rf_val_native_l I my.2.1 en x' y' T).mp hxy))
    have ea := fA.unique_l I ey ((rf_val_native_l I my.2.1 en x' a' A₀).mpr ha) xa
    have ef := fg₁.unique_l I ey ((rf_val_native_l I my.2.1 en x' f' G').mpr hf) xF
    have candidate := (rf_val_native_l I my.2.1 en a' y' f').mpr val
    exact ff.unique_l I ey (ea ▸ ef ▸ candidate) value
  obtain ⟨y, hxy⟩ := fT.value_l I ey hx hxw
  have atE : Rf_val_d I Y S x E₀ T.val := selected y hxy ▸ hxy
  exact ⟨fun h => ((fn0_function_l (ZF.modelsKP hZF) fs).1.2 n E E₀ h hnE).symm ▸ atE,
    fun h => (fT.unique_l I ey h atE).symm ▸ hnE⟩

end YesMetaZFC.SetTheory.Internal
