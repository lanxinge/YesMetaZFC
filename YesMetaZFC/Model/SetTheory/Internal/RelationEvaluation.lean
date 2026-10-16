import YesMetaZFC.Model.SetTheory.Internal.FunctionCode
import YesMetaZFC.Model.SetTheory.Internal.RelationRelative

/-! # 原关系中的函数码与求值

函数性和求值均解释为原关系模型中的固定公式；背景只存放对象码。
关系外延性用来读取函数的单值性，传递性仅用于识别旧隶属模型的函数图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rf_ext_d (X R : M.Domain) : Prop := ∀ x, M.mem x X → ∀ y, M.mem y X →
  (∀ z, M.mem z X → (M.PairMember I z x R ↔ M.PairMember I z y R)) → x = y

def rf_ext_m {d} (X R : Term d) : Formula 1 d := Formula.forallMem X
  (Formula.forallMem X.weaken (.imp (Formula.forallMem X.weaken.weaken
    (.iff (Formula.orderedPairMem 𝒞 .newest (.bound 2) R.weaken.weaken.weaken)
      (Formula.orderedPairMem 𝒞 .newest (.bound 1) R.weaken.weaken.weaken)))
    (Formula.extensionalEq (.bound 1) .newest)))
derive_free_closed rf_ext_m

theorem rf_ext_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X R : Term d) :
    Formula.satisfies ρ (rf_ext_m (𝒞 := 𝒞) X R) ↔ Rf_ext_d I (X.eval ρ) (R.eval ρ) := by
  simp only [rf_ext_m, Rf_ext_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]; rfl

theorem Rf_ext_d.native_l {X R} (h : Rf_ext_d I X R) (nx : ∃ x, M.mem x X) :
    Extensional (smdl_structure_l I (R := R) nx) :=
  ⟨fun x y same => Subtype.ext (h x.val x.property y.val y.property (fun z hz => same ⟨z, hz⟩))⟩

theorem rf_ext_mem_l (hE : Extensional M) {c X R} (hX : M.TransitiveSet X) (hm : Smem_d I c X R) :
    Rf_ext_d I X R := by
  intro x hx y hy same
  apply hE.eq_of_same_members x y
  intro z
  exact ⟨fun hz => ((hm.2 z y).mp ((same z (hX x hx z hz)).mp ((hm.2 z x).mpr ⟨hX x hx z hz, hx, hz⟩))).2.2,
    fun hz => ((hm.2 z x).mp ((same z (hX y hy z hz)).mpr ((hm.2 z y).mpr ⟨hX y hy z hz, hy, hz⟩))).2.2⟩

def Rf_val_d (X R p x f : M.Domain) : Prop := ∃ hp : M.mem p X, ∃ hx : M.mem x X, ∃ hf : M.mem f X,
  Formula.satisfies (⟨Fin.cases ⟨p, hp⟩ (Fin.cases ⟨x, hx⟩ (fun _ => ⟨f, hf⟩)), fun _ => ⟨f, hf⟩⟩ :
    Env (smdl_structure_l I (R := R) ⟨f, hf⟩) 3) (rd_entry0_m .newest (.bound 1) (.bound 2))

def Rf_fun_d (X R D f : M.Domain) : Prop := ∃ hD : M.mem D X, ∃ hf : M.mem f X,
  ∃ B : (smdl_structure_l I (R := R) ⟨D, hD⟩).Domain,
    Formula.satisfies (⟨Fin.cases ⟨D, hD⟩ (Fin.cases B (fun _ => ⟨f, hf⟩)), fun _ => ⟨f, hf⟩⟩ :
      Env (smdl_structure_l I (R := R) ⟨D, hD⟩) 3) (fn0_m .newest (.bound 1) (.bound 2))

def rf_val_m {d} (X R p x f : Term d) : Formula 1 d :=
  .conj (.mem p X) (.conj (.mem x X) (.conj (.mem f X)
    (rr_rel_m 𝒞 (n := 3) (rd_entry0_m .newest (.bound 1) (.bound 2)) X R (Fin.cases p (Fin.cases x (fun _ => f))))))

def rf_fun_m {d} (X R D f : Term d) : Formula 1 d :=
  .conj (.mem D X) (.conj (.mem f X) (Formula.existsMem X
    (rr_rel_m 𝒞 (n := 3) (fn0_m .newest (.bound 1) (.bound 2)) X.weaken R.weaken
      (Fin.cases D.weaken (Fin.cases .newest (fun _ => f.weaken))))))

@[simp] theorem rf_val_closed_l {d} (X R p x f : Term d) (hX : X.freeSupport = [])
    (hR : R.freeSupport = []) (hp : p.freeSupport = []) (hx : x.freeSupport = []) (hf : f.freeSupport = []) :
    (rf_val_m (𝒞 := 𝒞) X R p x f).FreeClosed := by
  exact ⟨⟨hp, hX⟩, ⟨⟨hx, hX⟩, ⟨⟨hf, hX⟩, rr_rel_closed_l 𝒞 _ (by simp -implicitDefEqProofs)
    X R _ hX hR (Fin.cases hp (Fin.cases hx (fun _ => hf)))⟩⟩⟩

@[simp] theorem rf_fun_closed_l {d} (X R D f : Term d) (hX : X.freeSupport = [])
    (hR : R.freeSupport = []) (hD : D.freeSupport = []) (hf : f.freeSupport = []) :
    (rf_fun_m (𝒞 := 𝒞) X R D f).FreeClosed := by
  exact ⟨⟨hD, hX⟩, ⟨⟨hf, hX⟩, ⟨⟨rfl, by simpa using hX⟩,
    rr_rel_closed_l 𝒞 _ (by simp -implicitDefEqProofs) _ _ _ (by simpa using hX) (by simpa using hR)
      (Fin.cases (by simpa using hD) (Fin.cases rfl (fun _ => by simpa using hf)))⟩⟩⟩

theorem rf_val_sat_l {d} (ρ : Env M d) (X R p x f : Term d) :
    Formula.satisfies ρ (rf_val_m (𝒞 := 𝒞) X R p x f) ↔
      Rf_val_d I (X.eval ρ) (R.eval ρ) (p.eval ρ) (x.eval ρ) (f.eval ρ) := by
  have read (hp : M.mem (p.eval ρ) (X.eval ρ)) (hx : M.mem (x.eval ρ) (X.eval ρ))
      (hf : M.mem (f.eval ρ) (X.eval ρ)) := rr_rel_sat_l I (R := R.eval ρ) ⟨f.eval ρ, hf⟩
    (rd_entry0_m (n := 3) .newest (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs)
    (⟨Fin.cases ⟨p.eval ρ, hp⟩ (Fin.cases ⟨x.eval ρ, hx⟩ (fun _ => ⟨f.eval ρ, hf⟩)), fun _ => ⟨f.eval ρ, hf⟩⟩)
    ρ X R (Fin.cases p (Fin.cases x (fun _ => f))) rfl rfl
    (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  change (_ ∧ _ ∧ _ ∧ _) ↔ ∃ hp hx hf, _
  exact ⟨fun ⟨hp, hx, hf, h⟩ => ⟨hp, hx, hf, (read hp hx hf).mp h⟩,
    fun ⟨hp, hx, hf, h⟩ => ⟨hp, hx, hf, (read hp hx hf).mpr h⟩⟩

theorem rf_fun_sat_l {d} (ρ : Env M d) (X R D f : Term d) :
    Formula.satisfies ρ (rf_fun_m (𝒞 := 𝒞) X R D f) ↔
      Rf_fun_d I (X.eval ρ) (R.eval ρ) (D.eval ρ) (f.eval ρ) := by
  have read (hD : M.mem (D.eval ρ) (X.eval ρ)) (hf : M.mem (f.eval ρ) (X.eval ρ))
      (B : M.Domain) (hB : M.mem B (X.eval ρ)) := rr_rel_sat_l I (R := R.eval ρ) ⟨D.eval ρ, hD⟩
    (fn0_m (n := 3) .newest (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs)
    (⟨Fin.cases ⟨D.eval ρ, hD⟩ (Fin.cases ⟨B, hB⟩ (fun _ => ⟨f.eval ρ, hf⟩)), fun _ => ⟨f.eval ρ, hf⟩⟩)
    (ρ.push B) X.weaken R.weaken (Fin.cases D.weaken (Fin.cases .newest (fun _ => f.weaken)))
    (by simp only [Definitional.Term.eval_weaken]) (by simp only [Definitional.Term.eval_weaken])
    (Fin.cases (Definitional.Term.eval_weaken ρ B D)
      (Fin.cases rfl (fun _ => Definitional.Term.eval_weaken ρ B f)))
  simp only [rf_fun_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, Rf_fun_d]
  exact ⟨fun ⟨hD, hf, B, hB, h⟩ => ⟨hD, hf, ⟨B, hB⟩, (read hD hf B hB).mp h⟩,
    fun ⟨hD, hf, B, h⟩ => ⟨hD, hf, B.val, B.property, (read hD hf B.val B.property).mpr h⟩⟩

theorem rf_val_native_l {X R} (nx : ∃ x, M.mem x X) (ext : Extensional (smdl_structure_l I (R := R) nx))
    (p x f : (smdl_structure_l I (R := R) nx).Domain) :
    Rf_val_d I X R p.val x.val f.val ↔ Rd_entry_d p x f := by
  exact ⟨fun ⟨_, _, _, h⟩ => (rd_entry0_sat_l ext ..).mp h,
    fun h => ⟨p.property, x.property, f.property, (rd_entry0_sat_l ext ..).mpr h⟩⟩

theorem rf_fun_native_l {X R} (nx : ∃ x, M.mem x X) (ext : Extensional (smdl_structure_l I (R := R) nx))
    (D f : (smdl_structure_l I (R := R) nx).Domain) :
    Rf_fun_d I X R D.val f.val ↔ ∃ B : (smdl_structure_l I (R := R) nx).Domain, Fn0_d D B f := by
  exact ⟨fun ⟨_, _, B, h⟩ => ⟨B, (fn0_sat_l ext ..).mp h⟩,
    fun ⟨B, h⟩ => ⟨D.property, f.property, B, (fn0_sat_l ext ..).mpr h⟩⟩

theorem rf_val_mem_l (hE : Extensional M) {c X R p x f} (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (hf : M.mem f X) : Rf_val_d I X R p x f ↔ Rd_entry_d p x f := by
  have read hp hx := (smem_delta_image_l I hm hX (rd_entry0_delta_l .newest (.bound 1) (.bound 2))
    (⟨Fin.cases ⟨p, hp⟩ (Fin.cases ⟨x, hx⟩ (fun _ => ⟨f, hf⟩)), fun _ => ⟨f, hf⟩⟩ :
      Env (smdl_structure_l I (R := R) hm.1.2.1) 3)).trans (rd_entry0_sat_l hE _ .newest (.bound 1) (.bound 2))
  exact ⟨fun ⟨hp, hx, _, h⟩ => (read hp hx).mp h, fun h =>
    ⟨(rd_entry_transitive_l hX hf h).1, (rd_entry_transitive_l hX hf h).2, hf, (read _ _).mpr h⟩⟩

theorem rf_fun_mem_l (hE : Extensional M) {c X R D f} (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (hD : M.mem D X) : Rf_fun_d I X R D f ↔ Sfun_d X D f := by
  have read hf (B : (smdl_structure_l I (R := R) hm.1.2.1).Domain) :=
    (smem_delta_image_l I hm hX (fn0_delta_l .newest (.bound 1) (.bound 2))
      (⟨Fin.cases ⟨D, hD⟩ (Fin.cases B (fun _ => ⟨f, hf⟩)), fun _ => ⟨f, hf⟩⟩ :
        Env (smdl_structure_l I (R := R) hm.1.2.1) 3)).trans (fn0_sat_l hE _ .newest (.bound 1) (.bound 2))
  exact ⟨fun ⟨_, hf, B, h⟩ => ⟨hf, B.val, B.property, (read hf B).mp h⟩,
    fun ⟨hf, B, hB, h⟩ => ⟨hD, hf, ⟨B, hB⟩, (read hf ⟨B, hB⟩).mpr h⟩⟩

theorem Rf_fun_d.mem_l {X R D f} (h : Rf_fun_d I X R D f) : M.mem f X :=
  h.elim fun _ h => h.elim fun hf _ => hf

theorem Rf_val_d.bounds_l {X R p x f} (h : Rf_val_d I X R p x f) : M.mem p X ∧ M.mem x X ∧ M.mem f X :=
  h.elim fun hp h => h.elim fun hx h => h.elim fun hf _ => ⟨hp, hx, hf⟩

theorem Rf_fun_d.value_l {X R D f p} (h : Rf_fun_d I X R D f) (ext : Rf_ext_d I X R)
    (hp : M.mem p X) (hd : M.PairMember I p D R) : ∃ x, Rf_val_d I X R p x f := by
  obtain ⟨hD, hf, B, funsat⟩ := h
  have en := ext.native_l I ⟨D, hD⟩
  have fn := (fn0_sat_l en _ .newest (.bound 1) (.bound 2)).mp funsat
  obtain ⟨x, _, hx⟩ := fn.2.1 ⟨p, hp⟩ hd
  exact ⟨x.val, (rf_val_native_l I ⟨D, hD⟩ en ⟨p, hp⟩ x ⟨f, hf⟩).mpr hx⟩

theorem Rf_fun_d.unique_l {X R D f p x y} (h : Rf_fun_d I X R D f) (ext : Rf_ext_d I X R)
    (hx : Rf_val_d I X R p x f) (hy : Rf_val_d I X R p y f) : x = y := by
  obtain ⟨hD, hf, B, funsat⟩ := h
  have en := ext.native_l I ⟨D, hD⟩
  have fn := (fn0_sat_l en _ .newest (.bound 1) (.bound 2)).mp funsat
  have px := (rf_val_native_l I ⟨D, hD⟩ en ⟨p, hx.bounds_l I |>.1⟩ ⟨x, hx.bounds_l I |>.2.1⟩ ⟨f, hf⟩).mp hx
  have py := (rf_val_native_l I ⟨D, hD⟩ en ⟨p, hy.bounds_l I |>.1⟩ ⟨y, hy.bounds_l I |>.2.1⟩ ⟨f, hf⟩).mp hy
  exact congrArg Subtype.val (fn.2.2 _ (fn.bound_l px).1 _ (fn.bound_l px).2 _ (fn.bound_l py).2 px py)

end YesMetaZFC.SetTheory.Internal
