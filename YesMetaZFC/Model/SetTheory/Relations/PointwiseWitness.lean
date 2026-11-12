import YesMetaZFC.Model.SetTheory.Types.PointwiseWitness
import YesMetaZFC.Model.SetTheory.Relations.Collection

/-! # 原始关系源中的存在行见证

先把“某个函数码在此点取值 y 且满足量词体”编成内部程序，再在当前定义域上统一见证 y。
所得一个内部函数在每个指定点给出量词体见证；不选择背景中的函数族。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_pe_witness_raw_l {ω c' Y S E F n r z i j b a}
    (hω : M.IsOmega ω) (model : Smdl_d I c' Y S)
    (D A : (smdl_structure_l I (R := S) model.2.1).Domain)
    (context : Pe_context_d I ω c' Y S D.val E)
    (uniform : Sc_uniform_d I ω Y S D.val)
    (hF : Sfm_d I ω n F) (hc : M.PairMember I r z F)
    (hs : Sop_d I 3 z i j) (hj : M.mem j n) (hb : M.mem b ω) (hB : Sbound_d I F b) (ha : M.mem a E)
    (total : ∀ p : (smdl_structure_l I (R := S) model.2.1).Domain,
      Rd_entry_d p.val D.val S → Rd_entry_d p.val A.val S → Pe_sat_d I b D.val Y S E F n r a p.val) :
    ∃ g C : (smdl_structure_l I (R := S) model.2.1).Domain, Fn0_d D C g ∧
      ∃ a', Senv_update_d I a i g.val a' ∧ ∀ p : (smdl_structure_l I (R := S) model.2.1).Domain,
        Rd_entry_d p.val D.val S → Rd_entry_d p.val A.val S → Pe_sat_d I b D.val Y S E F n j a' p.val := by
  let N := smdl_structure_l I (R := S) model.2.1
  have hE := context.2.2.1
  have en := context.1.native_l I model.2.1
  have hi := (hB.operands_l I hc hs).1
  have hiω := hω.transitive (ZF.modelsKP hZF) b hb i hi
  obtain ⟨t, ht, htω⟩ := hω.1.2 b hb
  obtain ⟨u, hu, huω⟩ := hω.1.2 t htω
  obtain ⟨v, hv, hvω⟩ := hω.1.2 u huω
  obtain ⟨σ, hσ, hσω⟩ := hω.1.2 v hvω
  have bt : M.MemberSubset b t := fun x hx => (ht x).mpr (Or.inl hx)
  have tu : M.MemberSubset t u := fun x hx => (hu x).mpr (Or.inl hx)
  have uv : M.MemberSubset u v := fun x hx => (hv x).mpr (Or.inl hx)
  have vσ : M.MemberSubset v σ := fun x hx => (hσ x).mpr (Or.inl hx)
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have bi : b ≠ i := fun eq => ir i (eq ▸ hi)
  have ti : t ≠ i := fun eq => ir i (eq ▸ bt i hi)
  have ui : u ≠ i := fun eq => ir i (eq ▸ tu i (bt i hi))
  have bt' : b ≠ t := fun eq => ir t (eq ▸ ht.predecessor_mem)
  have bu : b ≠ u := fun eq => ir u (eq ▸ tu b ht.predecessor_mem)
  have tu' : t ≠ u := fun eq => ir u (eq ▸ hu.predecessor_mem)
  obtain ⟨m, G, T, compile⟩ := pe_compile_bound_l hZF hω hF hb hB ht
  obtain ⟨k, hk, hjk⟩ := compile.2.1.2.2 j hj
  obtain ⟨n₁, F₁, r₁, h₁, a₁⟩ := sfm_function_raw_l I hZF hω compile.1 hσω
    (vσ i (uv i (tu i (bt i hi)))) (vσ b (uv b (tu b ht.predecessor_mem))) hσ.predecessor_mem
    (fun eq => ir b (eq ▸ uv b (tu b ht.predecessor_mem))) (fun eq => ir i (eq ▸ uv i (tu i (bt i hi))))
  let φ : Formula 1 3 := rd_entry0_m .newest (.bound 1) (.bound 2)
  let w : Fin 3 → M.Domain := Fin.cases t (Fin.cases u (fun _ => i))
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_template_l I hZF hω h₁.program φ (by simp -implicitDefEqProofs [φ]) w hσω
    (Fin.cases (vσ t (uv t hu.predecessor_mem)) (Fin.cases (vσ u hv.predecessor_mem) (fun _ => vσ i (uv i (tu i (bt i hi))))))
  obtain ⟨n₃, F₃, r₃, h₃, a₃⟩ := sfm_and_l I hZF hω h₂.program (h₂.span r₁ h₁.root) h₂.root
  obtain ⟨n₄, F₄, r₄, h₄, a₄⟩ := sfm_and_l I hZF hω h₃.program h₃.root (h₃.span k (h₂.span k (h₁.span k hk)))
  obtain ⟨n₅, F₅, r₅, h₅, a₅⟩ := sfm_ex_l I hZF hω h₄.program hiω h₄.root
  obtain ⟨aD, hDa, haD⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hb D.property
  obtain ⟨V, hV⟩ := seval_exists_l I hZF Y S E F hF.2.1.1
  have matrix (p x : N.Domain) f f' (hp : Rd_entry_d p.val D.val S)
      (hf : M.mem f E) (he : Pe_assign_d I b D.val Y S a f p.val) (hff : Senv_update_d I f i x.val f') :
      Sbin_d I Y S E F₅ n₅ r₅ t u aD p.val x.val ↔ Ssat_d I Y S E F n j f' := by
    obtain ⟨aT, hT, haT⟩ := senv_update_exists_l I hZF haD htω p.property
    obtain ⟨aU, hU, haU⟩ := senv_update_exists_l I hZF haT huω x.property
    have agree : Senv_agree_d I b a aU := fun s y hsb =>
      (hDa.agree_l I (ir b) s y hsb).trans ((hT.agree_l I (fun h => ir t (bt t h)) s y hsb).trans
        (hU.agree_l I (fun h => ir u (tu u (bt u h))) s y hsb))
    have params (g : N.Domain) aG (hG : Senv_update_d I aU i g.val aG) :
        Rd_entry_d b D.val aG ∧ Rd_entry_d t p.val aG ∧ Rd_entry_d u x.val aG ∧ Rd_entry_d i g.val aG :=
      ⟨(hG.2 b D.val).mpr (Or.inr ⟨bi, (hU.2 b D.val).mpr (Or.inr ⟨bu,
        (hT.2 b D.val).mpr (Or.inr ⟨bt', (hDa.2 b D.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩)⟩),
       (hG.2 t p.val).mpr (Or.inr ⟨ti, (hU.2 t p.val).mpr (Or.inr ⟨tu', (hT.2 t p.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩),
       (hG.2 u x.val).mpr (Or.inr ⟨ui, (hU.2 u x.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩),
       (hG.2 i g.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩
    have body (g : N.Domain) aG (hG : Senv_update_d I aU i g.val aG) :
        Ssat_d I Y S E F₄ n₄ r₄ aG ↔
          (Rf_fun_d I Y S D.val g.val ∧ Rf_val_d I Y S p.val x.val g.val) ∧ Ssat_d I Y S E G m k aG := by
      have hge := (hE aG).mpr (hG.function_l I haU hiω g.property)
      obtain ⟨bd, tp, ux, ig⟩ := params g aG hG
      let ρ : Env N 3 := ⟨Fin.cases p (Fin.cases x (fun _ => g)), fun _ => g⟩
      have atom := (a₂ Y S model.2.1 E hE aG hge ρ (Fin.cases tp (Fin.cases ux (fun _ => ig)))).trans
        ((rd_entry0_sat_l en ρ .newest (.bound 1) (.bound 2)).trans (rf_val_native_l I model.2.1 en p x g).symm)
      rw [a₄ Y S E aG hge, a₃ Y S E aG hge, ← h₂.sat_l I hZF h₁.program h₁.root Y S E aG,
        a₁ Y S E c' aG model g D en hE hge ig bd, atom,
        ← h₃.sat_l I hZF h₂.program (h₂.span k (h₁.span k hk)) Y S E aG,
        ← h₂.sat_l I hZF h₁.program (h₁.span k hk) Y S E aG, ← h₁.sat_l I hZF compile.1 hk Y S E aG]
      exact and_congr (and_congr (rf_fun_native_l I model.2.1 en D g).symm Iff.rfl) Iff.rfl
    have row (g : N.Domain) aG (hG : Senv_update_d I aU i g.val aG)
        (fn : Rf_fun_d I Y S D.val g.val) (val : Rf_val_d I Y S p.val x.val g.val) :=
      compile.2.2 c' Y S D.val E context j k hjk p.val aG f' hp
        ((hE aG).mpr (hG.function_l I haU hiω g.property))
        ((hE f').mpr (hff.function_l I ((hE f).mp hf) hiω x.property))
        (params g aG hG).1 (params g aG hG).2.1 ((he.congr_left_l I agree).update_l I fn val hG hff)
    apply (sbin_value_l I hZF.1 hT hU).trans
    rw [a₅ Y S E aU ((hE aU).mpr haU)]
    constructor
    · rintro ⟨g, aG, hg, hG, truth⟩
      obtain ⟨⟨fn, val⟩, truth⟩ := (body ⟨g, hg⟩ aG hG).mp truth
      exact (row ⟨g, hg⟩ aG hG fn val).mpr truth
    · intro truth
      obtain ⟨g, fn, val⟩ := context.2.2.2.2 x.val x.property
      obtain ⟨aG, hG, _⟩ := senv_update_exists_l I hZF haU hiω (fn.mem_l I)
      exact ⟨g, aG, fn.mem_l I, hG, (body ⟨g, fn.mem_l I⟩ aG hG).mpr
        ⟨⟨fn, val p.val p.property hp⟩, (row ⟨g, fn.mem_l I⟩ aG hG fn (val p.val p.property hp)).mp truth⟩⟩
  obtain ⟨g, C, fn, select⟩ := uniform.on_l I hZF hω model.2.1 D A hE h₅.program h₅.root
    htω huω tu' ((hE aD).mpr haD) (fun p hp hpA => by
      obtain ⟨f, hf, he, truth⟩ := total p hp hpA
      obtain ⟨x, f', hx, hff, truth⟩ := (ssat_exists_l I hZF hF hV hc hs hf).mp truth
      exact ⟨⟨x, hx⟩, (matrix p ⟨x, hx⟩ f f' hp hf he hff).mpr truth⟩)
  have fg := (rf_fun_native_l I model.2.1 en D g).mpr ⟨C, fn⟩
  obtain ⟨a', update, _⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hiω g.property
  refine ⟨g, C, fn, a', update, fun p hp hpA => ?_⟩
  obtain ⟨f, hf, he, _⟩ := total p hp hpA
  obtain ⟨x, _, hpx⟩ := fn.2.1 p hp
  obtain ⟨f', hff, hf'⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hiω x.property
  exact ⟨f', (hE f').mpr hf', he.update_l I fg ((rf_val_native_l I model.2.1 en p x g).mpr hpx) update hff,
    (matrix p x f f' hp hf he hff).mp (select p x hpx hpA)⟩

end YesMetaZFC.SetTheory.Internal
