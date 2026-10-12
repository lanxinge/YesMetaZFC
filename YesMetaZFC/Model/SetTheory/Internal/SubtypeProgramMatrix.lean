import YesMetaZFC.Model.SetTheory.Internal.SubtypeQuery
import YesMetaZFC.Model.SetTheory.Internal.SourceRelative

/-! # 子类型程序编译性质的一阶矩阵

七个槽仅是固定模板的参数表；被打包的原变量数仍是任意内部自然数。
相对化展开定义原子后，矩阵与已有打包编译器的完整语义逐字等价。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

def ts_values_m {d} (Y p v₀ v₁ v₂ v₃ v₄ v₅ v₆ : Term d) : Formula 1 d :=
  sr_rel_m ts_template_m Y (Fin.cases p (Fin.cases v₀ (Fin.cases v₁ (Fin.cases v₂
    (Fin.cases v₃ (Fin.cases v₄ (Fin.cases v₅ (fun _ => v₆))))))))
@[simp] theorem ts_values_closed_l {d} (Y p v₀ v₁ v₂ v₃ v₄ v₅ v₆ : Term d)
    (hY : Y.freeSupport = []) (hp : p.freeSupport = []) (h₀ : v₀.freeSupport = [])
    (h₁ : v₁.freeSupport = []) (h₂ : v₂.freeSupport = []) (h₃ : v₃.freeSupport = [])
    (h₄ : v₄.freeSupport = []) (h₅ : v₅.freeSupport = []) (h₆ : v₆.freeSupport = []) :
    (ts_values_m Y p v₀ v₁ v₂ v₃ v₄ v₅ v₆).FreeClosed :=
  sr_rel_closed_l ts_template_m ts_template_closed_l Y _ hY (Fin.cases hp (Fin.cases h₀
    (Fin.cases h₁ (Fin.cases h₂ (Fin.cases h₃ (Fin.cases h₄ (Fin.cases h₅ (fun _ => h₆))))))))

def ts_compile_m {d} (ω n a : Term d) (σ : Fin 7 → Term d) : Formula 1 d := set[d] ⟪∀ η Y c R f g v₀ v₁ v₂ v₃ v₄ v₅ v₆,
  ⌜v_m kpair_convention_l⌝ₚ(η, Y) → ⌜ω⌝ₛ ∈ Y → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(f, ⌜ω⌝ₛ, Y) →
  ⌜Formula.isFunctionFromTo FlatPairing.convention⌝ₚ(g, ⌜ω⌝ₛ, Y) →
  ⌜sx_graph_m (𝒞 := kpair_convention_l) (𝒟 := FlatPairing.convention)⌝ₚ(f, g) →
  ⌜rd_entry0_m⌝ₚ(⌜σ 6⌝ₛ, ⌜ω⌝ₛ, f) →
  ⌜rd_entry0_m⌝ₚ(⌜σ 0⌝ₛ, v₀, f) → ⌜rd_entry0_m⌝ₚ(⌜σ 1⌝ₛ, v₁, f) →
  ⌜rd_entry0_m⌝ₚ(⌜σ 2⌝ₛ, v₂, f) → ⌜rd_entry0_m⌝ₚ(⌜σ 3⌝ₛ, v₃, f) →
  ⌜rd_entry0_m⌝ₚ(⌜σ 4⌝ₛ, v₄, f) → ⌜rd_entry0_m⌝ₚ(⌜σ 5⌝ₛ, v₅, f) → ⌜rd_entry0_m⌝ₚ(⌜σ 6⌝ₛ, v₆, f) →
    (⌜satisfies_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, c, ⌜a⌝ₛ, f) ↔ ∃ p ∈ Y,
      ⌜fs_code_m (𝒞 := FlatPairing.convention)⌝ₚ(⌜ω⌝ₛ, Y, g, ⌜n⌝ₛ, p) ∧
      ⌜ts_values_m⌝ₚ(Y, p, v₀, v₁, v₂, v₃, v₄, v₅, v₆))⟫

@[simp] theorem ts_compile_closed_l {d} (ω n a : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (ha : a.freeSupport = [])
    (hσ : ∀ j, (σ j).freeSupport = []) : (ts_compile_m ω n a σ).FreeClosed := by
  simp -implicitDefEqProofs [ts_compile_m, Definitional.Formula.FreeClosed, hw, hn, ha, hσ]

def Ts_compile_d (ω n a : M.Domain) (σ : Fin 7 → M.Domain) : Prop :=
  ∀ η Y c R f g (model : Smem_d I c Y R) (ρ : Env (smdl_structure_l I (R := R) model.1.2.1) 7),
    V_d I η Y → M.mem ω Y → M.IsSetFunctionFromTo I f ω Y → M.IsSetFunctionFromTo K g ω Y →
    Sx_graph_d I K f g → Rd_entry_d (σ 6) ω f → (∀ j, Rd_entry_d (σ j) (ρ.bound j).val f) →
      (Satisfies_d I ω c a f ↔ ∃ p : (smdl_structure_l I (R := R) model.1.2.1).Domain,
        Fs_code_d K ω Y g n p.val ∧ Formula.satisfies (ρ.push p) ts_template_m)

private theorem ts_values_sat_l {Y : M.Domain} (ny : Nonempty {x // M.mem x Y}) {d}
    (θ : Env M d) (T p v₀ v₁ v₂ v₃ v₄ v₅ v₆ : Term d) (ρ : Env (rt_model_l Y ny) 7)
    (x : (rt_model_l Y ny).Domain) (hY : T.eval θ = Y) (hp : p.eval θ = x.val)
    (hv : ∀ j, ((Fin.cases v₀ (Fin.cases v₁ (Fin.cases v₂ (Fin.cases v₃
      (Fin.cases v₄ (Fin.cases v₅ (fun _ => v₆)))))) : Fin 7 → Term d) j).eval θ = (ρ.bound j).val) :
    Formula.satisfies θ (ts_values_m T p v₀ v₁ v₂ v₃ v₄ v₅ v₆) ↔ Formula.satisfies (ρ.push x) ts_template_m :=
  sr_rel_sat_l ny ts_template_m ts_template_closed_l (ρ.push x) θ T _ hY (Fin.cases hp hv)

theorem ts_compile_sat_l {d} (θ : Env M d) (ω n a : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies θ (ts_compile_m ω n a σ) ↔
      Ts_compile_d hZF (ω.eval θ) (n.eval θ) (a.eval θ) (fun j => (σ j).eval θ) := by
  simp only [ts_compile_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    v_sat_l I hZF.1, Formula.satisfies_mem_iff, smem_sat_l I,
    Formula.satisfies_isFunctionFromTo_iff I hZF.1, Formula.satisfies_isFunctionFromTo_iff K hZF.1,
    sx_graph_sat_l I K, rd_entry0_sat_l hZF.1, Formula.satisfies_iff_iff, satisfies_sat_l I hZF.1,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, fs_code_sat_l K hZF.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · intro h η Y c R f g model ρ hY hw ff fg same fw values
    have read := h η Y c R f g (ρ.bound 0).val (ρ.bound 1).val (ρ.bound 2).val (ρ.bound 3).val
      (ρ.bound 4).val (ρ.bound 5).val (ρ.bound 6).val hY hw model ff fg same fw
      (values 0) (values 1) (values 2) (values 3) (values 4) (values 5) (values 6)
    refine read.trans ?_
    let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω.eval θ, hw⟩⟩
    let ρ' : Env (rt_model_l Y ny) 7 := ⟨ρ.bound, ρ.free⟩
    let ξ (p : M.Domain) := (((((((((((((θ.push η).push Y).push c).push R).push f).push g).push (ρ.bound 0).val).push
      (ρ.bound 1).val).push (ρ.bound 2).val).push (ρ.bound 3).val).push (ρ.bound 4).val).push (ρ.bound 5).val).push (ρ.bound 6).val).push p
    have atom (p : (rt_model_l Y ny).Domain) :=
      (ts_values_sat_l ny (ξ p.val) (.bound 12) .newest (.bound 7) (.bound 6) (.bound 5) (.bound 4)
        (.bound 3) (.bound 2) (.bound 1) ρ' p rfl rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))).trans
        (smem_formula_l I model ny ts_template_m (ρ'.push p))
    exact ⟨fun ⟨p, hp, cp, truth⟩ => ⟨⟨p, hp⟩, cp, (atom ⟨p, hp⟩).mp truth⟩,
      fun ⟨p, cp, truth⟩ => ⟨p.val, p.property, cp, (atom p).mpr truth⟩⟩
  · intro h η Y c R f g v₀ v₁ v₂ v₃ v₄ v₅ v₆ hY hw model ff fg same fw h₀ h₁ h₂ h₃ h₄ h₅ h₆
    let v : Fin 7 → M.Domain := Fin.cases v₀ (Fin.cases v₁ (Fin.cases v₂ (Fin.cases v₃
      (Fin.cases v₄ (Fin.cases v₅ (fun _ => v₆))))))
    have values : ∀ j, Rd_entry_d ((σ j).eval θ) (v j) f := Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂
      (Fin.cases h₃ (Fin.cases h₄ (Fin.cases h₅ (Fin.cases h₆ (fun j => Fin.elim0 j)))))))
    let ρ : Env (smdl_structure_l I (R := R) model.1.2.1) 7 :=
      ⟨fun j => ⟨v j, ff.output_mem_of_pairMember (values j)⟩, fun _ => ⟨ω.eval θ, hw⟩⟩
    refine (h η Y c R f g model ρ hY hw ff fg same fw values).trans ?_
    let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω.eval θ, hw⟩⟩
    let ρ' : Env (rt_model_l Y ny) 7 := ⟨ρ.bound, ρ.free⟩
    let ξ (p : M.Domain) := (((((((((((((θ.push η).push Y).push c).push R).push f).push g).push v₀).push v₁).push v₂).push v₃).push v₄).push v₅).push v₆).push p
    have atom (p : (rt_model_l Y ny).Domain) :=
      (ts_values_sat_l ny (ξ p.val) (.bound 12) .newest (.bound 7) (.bound 6) (.bound 5) (.bound 4)
        (.bound 3) (.bound 2) (.bound 1) ρ' p rfl rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))).trans
        (smem_formula_l I model ny ts_template_m (ρ'.push p))
    exact ⟨fun ⟨p, cp, truth⟩ => ⟨p.val, p.property, cp, (atom p).mpr truth⟩,
      fun ⟨p, hp, cp, truth⟩ => ⟨⟨p, hp⟩, cp, (atom ⟨p, hp⟩).mp truth⟩⟩

end YesMetaZFC.SetTheory.Internal
