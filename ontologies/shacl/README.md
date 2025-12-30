# ARM Boot Ontology - SHACL Validation Shapes

**Generated**: 2025-12-27
**Validator**: pySHACL 0.30.1

## Overview

This directory contains SHACL (Shapes Constraint Language) shapes for validating the ARM bootloader ontologies. SHACL provides data quality validation by checking that RDF data conforms to expected structures.

## Files

| File | Description | Target Ontology |
|------|-------------|-----------------|
| `arm_boot_shapes.ttl` | FSA validation shapes | arm_boot_fsa_ontology.n3 |
| `arm_boot_category_shapes.ttl` | Category theory shapes | arm_boot_grothendieck_category.n3 |

## Quick Start

```bash
# Validate FSA ontology
pyshacl -s arm_boot_shapes.ttl -df turtle ../arm_boot_fsa_ontology.n3

# Validate category ontology (OWL format)
pyshacl -s arm_boot_category_shapes.ttl -df xml ../owl_format/arm_boot_grothendieck_category.owl

# Verbose output
pyshacl -s arm_boot_shapes.ttl -df turtle ../arm_boot_fsa_ontology.n3 -f human

# Output validation report as Turtle
pyshacl -s arm_boot_shapes.ttl -df turtle ../arm_boot_fsa_ontology.n3 -f turtle
```

## Validation Results

### FSA Ontology
```
Validation Report
Conforms: True
```

### Category Theory Ontology
```
Validation Report
Conforms: False
Results (1):
  Constraint Violation: AnyToFailure morphism has domain BootStateObjects (class)
                        instead of an Object instance
```

This violation indicates a data modeling issue to address.

## Shapes Defined

### arm_boot_shapes.ttl

| Shape | Target | Validations |
|-------|--------|-------------|
| `StateShape` | `boot:State` | Must have description (string, min 5 chars) |
| `TransitionShape` | `boot:Transition` | Must have fromState, toState (both State class) |
| `ConditionShape` | `boot:Condition` | Must have description |
| `RaspberryPiModelShape` | `boot:RaspberryPiModel` | Must have cpuArchitecture, valid values |
| `FindingShape` | `boot:Finding` | Must have findingType and description |
| `BootFSAShape` | `boot:BootFSA` | Must have at least one state and transition |
| `NoSelfLoopShape` | `boot:Transition` | SPARQL: No self-loops (warning) |

### arm_boot_category_shapes.ttl

| Shape | Target | Validations |
|-------|--------|-------------|
| `CategoryShape` | `cat:Category` | Must have label |
| `ObjectShape` | `cat:Object` | Should have label |
| `MorphismShape` | `cat:Morphism` | Must have domain and codomain (Object class) |
| `IdentityMorphismShape` | `cat:StateIdentityMorphisms` | SPARQL: domain = codomain |
| `FunctorShape` | `cat:Functor` | Should have source/target category |
| `NaturalTransformationShape` | `cat:NaturalTransformation` | Must have label |
| `UniversalPropertyShape` | `cat:UniversalProperty` | Must have characterizedBy |
| `ToposShape` | `cat:Topos` | Should have hasPowerObjects, hasSubobjectClassifier |
| `CategoryAxiomShape` | `cat:CategoryAxiom` | Must have statement |

## Constraint Types Used

### Property Constraints
- `sh:minCount` / `sh:maxCount` - Cardinality
- `sh:datatype` - Value type (xsd:string, xsd:boolean, etc.)
- `sh:class` - Object type constraint
- `sh:minLength` - Minimum string length
- `sh:in` - Enumerated values

### SPARQL Constraints
- Custom SPARQL queries for complex validations
- Used for: self-loop detection, domain=codomain for identity morphisms

### Severity Levels
- `sh:Violation` (default) - Must fix
- `sh:Warning` - Should fix

## Adding Custom Shapes

```turtle
@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix boot: <http://example.org/arm-boot-fsa#> .

shapes:MyCustomShape a sh:NodeShape ;
    sh:targetClass boot:MyClass ;
    sh:property [
        sh:path boot:myProperty ;
        sh:minCount 1 ;
        sh:datatype xsd:string ;
        sh:message "Custom error message"
    ] .
```

## Integration with CI/CD

```bash
#!/bin/bash
# validate_ontologies.sh

pyshacl -s shacl/arm_boot_shapes.ttl -df turtle arm_boot_fsa_ontology.n3
if [ $? -ne 0 ]; then
    echo "FSA ontology validation failed"
    exit 1
fi

echo "All validations passed"
```

## Comparison with Other Validation

| Tool | Type | Best For |
|------|------|----------|
| pySHACL | Data validation | Cardinality, types, custom rules |
| HermiT | OWL reasoning | Consistency, classification |
| Z3 | SMT | State machine properties |
| Vampire | FOL | Theorem proving |

**Recommendation**: Use SHACL for data quality validation before running reasoners.

## Troubleshooting

### N3 Parse Errors
Some ontologies may have N3 syntax issues. Use the OWL/RDF-XML format:
```bash
pyshacl -s shapes.ttl -df xml ../owl_format/ontology.owl
```

### Missing Prefixes
Ensure the data file and shapes file use compatible prefixes.

---

**Last Updated**: 2025-12-27
